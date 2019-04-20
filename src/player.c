// ffmpeg
#include <libavcodec/avcodec.h>
#include <libavformat/avformat.h>
#include <libavformat/avio.h>
#include <libavutil/avutil.h>

#include <libavutil/samplefmt.h>
#include "bcm_host.h"
#include "ilclient.h"
#include "rpi_mp.h"
#include "rpi_mp_packet_buffer.h"
#include "rpi_mp_utils.h"

#define FIFO_SLEEPY_TIME               10000

/* OMX Component ports --------------------- */
enum omxports
{
	VIDEO_DECODE_INPUT_PORT     = 130,
	VIDEO_DECODE_OUT_PORT       = 131,
	VIDEO_RENDER_INPUT_PORT     =  90,
	VIDEO_SCHEDULER_INPUT_PORT  =  10,
	VIDEO_SCHEDULER_OUT_PORT    =  11,
	VIDEO_SCHEDULER_CLOCK_PORT  =  12,
	EGL_RENDER_INPUT_PORT       = 220,
	EGL_RENDER_OUT_PORT         = 221,
	CLOCK_VIDEO_PORT            =  80,
};

/* FLAGS ----------------------------------- */
enum flags
{
	STOPPED               = 0x0001,
	PAUSED                = 0x0002,
	FIRST_VIDEO           = 0x0004,
	FIRST_AUDIO           = 0x0008,
	PORT_SETTINGS_CHANGED = 0x0010,
	HARDWARE_DECODE_AUDIO = 0x0020,
	DONE_READING          = 0x0040,
	VIDEO_STOPPED         = 0x0080,
	LAST_BUFFER           = 0x0100,
	LAST_FRAME            = 0x0200,
	CLOCK_PAUSED          = 0x0400,
	LOOP_VIDEO            = 0x0800,
};

#define OUT_CHANNELS(num_channels) ((num_channels) > 4 ? 8 : (num_channels) > 2 ? 4 : (num_channels))
#define WAIT_WHILE_PAUSED { pthread_mutex_lock (&pause_mutex); ret = pthread_cond_wait (&pause_condition, &pause_mutex); pthread_mutex_unlock (&pause_mutex); }
// #define WAIT_WHILE_PAUSED {}
#define SET_FLAG(flag) { pthread_mutex_lock (&flags_mutex); flags |= flag; pthread_mutex_unlock (&flags_mutex); }
#define UNSET_FLAG(flag) { pthread_mutex_lock (&flags_mutex); flags &= ~flag; pthread_mutex_unlock (&flags_mutex); }
#define OMX_INIT_PARAM(type) memset (&type, 0x0, sizeof (type)); type.nSize = sizeof (type); type.nVersion.nVersion = OMX_VERSION;
#define OMX_INIT_STRUCTURE(a) \
    memset(&(a), 0, sizeof(a)); \
    (a).nSize = sizeof(a); \
    (a).nVersion.nVersion = OMX_VERSION

// Demuxing variables (ffmpeg)
static AVFormatContext      * fmt_ctx          = NULL;
static AVCodecContext       * video_codec_ctx  = NULL;
static AVStream             * video_stream     = NULL;
static int                    video_stream_idx =   -1;
static AVPacket               av_packet,
                              video_packet;
static AVFrame              * av_frame;

// Decoding variables (OMX)
static COMPONENT_T          * video_decode    = NULL,
                            * video_scheduler = NULL,
                            * video_clock     = NULL,
                            * egl_render      = NULL;

static TUNNEL_T               video_tunnel[4]; // last component must be NULL
static COMPONENT_T          * list[5]; // last component must be NULL
static ILCLIENT_T           * client;

static OMX_BUFFERHEADERTYPE * omx_video_buffer,
                            * omx_egl_buffers[BUFFER_COUNT];

static void                 * egl_images[BUFFER_COUNT];
static int                  * current_texture = NULL;
static int32_t                flags     =  0;
static unsigned int           refresh_rate = 0;
static int                    video_duration = 0;
static int                    current_buffer = 0;
static unsigned long          timer = 0;
// static int                    delta_time = 0;

static packet_buffer          video_packet_fifo;

// Thread variables
static pthread_mutex_t flags_mutex        = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t pause_mutex        = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t video_mutex        = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t  pause_condition    = PTHREAD_COND_INITIALIZER;
static pthread_mutex_t buffer_filled_mut  = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t  buffer_filled_cond = PTHREAD_COND_INITIALIZER;


/**
 *  Convert PTS (from libFFmpeg) to OMX_TICKS struct.
 */
static inline OMX_TICKS pts__omx_timestamp (int64_t pts)
{
	OMX_TICKS ticks;
	ticks.nLowPart 	= pts;
	ticks.nHighPart = pts >> 32;
	return ticks;
}

/**
 *	Converts AVPacket timestamp to an OMX_TICKS timestamp
 */
static inline OMX_TICKS omx_timestamp (AVPacket p)
{
	int64_t pts = p.pts != AV_NOPTS_VALUE ? p.pts : p.dts != AV_NOPTS_VALUE ? p.dts : 0;
	int      num = fmt_ctx->streams[p.stream_index]->time_base.num;
	int      den = fmt_ctx->streams[p.stream_index]->time_base.den;

	int64_t timestamp = ( pts * num * AV_TIME_BASE ) / den;
	return pts__omx_timestamp (timestamp);
}

/**
 *	Converts AVPacket timestamp to int64_t
 */
static inline int64_t int64_timestamp (AVPacket p)
{
	int64_t pts = p.pts != AV_NOPTS_VALUE ? p.pts : p.dts != AV_NOPTS_VALUE ? p.dts : 0;
	int64_t      num = fmt_ctx->streams[p.stream_index]->time_base.num;
	int64_t      den = fmt_ctx->streams[p.stream_index]->time_base.den;

	return ( pts * num * AV_TIME_BASE ) / den;
}

/**
 *  Lock decoding threads, i.e. pause.
 */
static inline void lock ()
{
	pthread_mutex_lock (&video_mutex);
}

/**
 *  Unlock decoding threads, i.e. unpause.
 */
static inline void unlock ()
{
	pthread_mutex_unlock (&video_mutex);
}

static int setup_clock ()
{
	int ret = 0;

	// set clock configuration
	OMX_TIME_CONFIG_CLOCKSTATETYPE clock_state;
	OMX_INIT_STRUCTURE(clock_state);
	clock_state.eState            = OMX_TIME_ClockStateWaitingForStartTime;
	clock_state.nWaitMask         = 0;

	// Preroll 0 ms,    from the second pass frames 2 & 3 are skipped, last 2 frames are not displayed
	// Preroll -200 ms, from the second pass last 2 frames are not displayed
	clock_state.nOffset			  = pts__omx_timestamp (0LL * 1000);
	// clock_state.nOffset			  = pts__omx_timestamp (-200LL * 1000);

	if (video_stream_idx != AVERROR_STREAM_NOT_FOUND)
		clock_state.nWaitMask = OMX_CLOCKPORT0;

	if (video_clock != NULL && OMX_SetParameter (ILC_GET_HANDLE (video_clock), OMX_IndexConfigTimeClockState, &clock_state) != OMX_ErrorNone)
	{
		fprintf (stderr, "Error settings parameters for video clock\n");
		ret = -13;
	}

	return ret;
}


/**
 *  Fill the EGL render buffer with decoded raw image data.
 *  Should only be called as callback for the fillbuffer event when video decoding
 *  of a frame is finished.
 */
void printState(OMX_HANDLETYPE handle)
{
	OMX_STATETYPE state;
	OMX_ERRORTYPE err;
	err = OMX_GetState(handle, &state);
	if (err != OMX_ErrorNone)
	{
		fprintf(stderr, "Error on getting state\n");
		exit(1);
	}
	switch (state)
	{
		case OMX_StateLoaded: printf("StateLoaded\n"); break;
		case OMX_StateIdle: printf("StateIdle\n"); break;
		case OMX_StateExecuting: printf("StateExecuting\n"); break;
		case OMX_StatePause: printf("StatePause\n"); break;
		case OMX_StateWaitForResources: printf("StateWait\n"); break;
		case OMX_StateInvalid: printf("StateInvalid\n"); break;
		default: printf("State unknown\n"); break;
	}
}

static void fill_egl_texture_buffer (void* data, COMPONENT_T* c)
{
	printf("CALLBACK: %i %i\n", omx_egl_buffers[current_buffer]->nFlags, omx_egl_buffers[current_buffer]->nTimeStamp.nLowPart);

	if (omx_egl_buffers[current_buffer]->nFlags != 1)
	{
		// Sync to refresh of the monitor
		// TODO: only activate if i.e. Refresh mon = 60, video fps = 59.94 or 29.97

		// delta_time = time_us() - timer;
		// printf("%lu ", delta_time / 1000);

		// int drift = (12666 - delta_time % 16666 ) / 10;
		// if (drift > 200) drift = 200;
		// if (drift < -200) drift = -200;
		// if ((drift < 10) && (drift > -10)) drift = 0;
		// printf("%lu %lu %d drift: %d\n",time_us(), timer, delta_time / 1000, drift);
		// printf("%d drift: %d\n", delta_time / 1000, drift);


		// if (~flags & PAUSED)
		// {
		// 	OMX_TIME_CONFIG_SCALETYPE scale;
		// 	OMX_INIT_STRUCTURE(scale);
		// 	scale.xScale 			= (1 << 16);
		// 	// scale.xScale 			= 65536 - drift;

		// 	OMX_ERRORTYPE omx_error;
		// 	if ((omx_error = OMX_SetParameter (ILC_GET_HANDLE (video_clock), OMX_IndexConfigTimeScale, &scale)) != OMX_ErrorNone)
		// 		fprintf (stderr, "Could not set scale parameter on video clock. Error 0x%08x\n", omx_error);
		// }

		current_buffer = (current_buffer + 1) % BUFFER_COUNT;
		pthread_mutex_lock (&buffer_filled_mut);
		*current_texture = (*current_texture + 1) % BUFFER_COUNT;
		pthread_mutex_unlock (&buffer_filled_mut);

		int err = OMX_FillThisBuffer (ILC_GET_HANDLE (egl_render), omx_egl_buffers[current_buffer]);
		if ( err != OMX_ErrorNone )
			fprintf (stderr, "OMX_FillThisBuffer failed for egl buffer in callback\n");
	}
}


void tick ()
{
	timer = time_us();
}

/**
 *	Decodes the current AVPacket as containing video data.
 *  @return int 0 on success, non-zero on error
 */
static inline int decode_video_packet ()
{
	int packet_size = 0;
	int64_t timestamp = int64_timestamp (video_packet);

	printf("DEC: Timestamp %llu\n", timestamp );

	while (video_packet.size > 0)
	{
		if ((omx_video_buffer = ilclient_get_input_buffer (video_decode, VIDEO_DECODE_INPUT_PORT, 1)) == NULL)
		{
			fprintf (stderr, "Error getting buffer to video decoder\n");
			return 1;
		}
		packet_size                  = video_packet.size > omx_video_buffer->nAllocLen ? omx_video_buffer->nAllocLen : video_packet.size;
		omx_video_buffer->nFilledLen = packet_size;
		omx_video_buffer->nOffset    = 0;
		omx_video_buffer->nFlags     = 0;

		// copy data to buffer
		memcpy (omx_video_buffer->pBuffer, video_packet.data, packet_size);
		video_packet.size -= packet_size;
		video_packet.data += packet_size;

		if (flags & FIRST_VIDEO)
		{
			printf("DEC: FIRST_VIDEO\n");
			omx_video_buffer->nFlags = OMX_BUFFERFLAG_STARTTIME | OMX_BUFFERFLAG_DISCONTINUITY;
			UNSET_FLAG (FIRST_VIDEO);
		}

		omx_video_buffer->nTimeStamp = pts__omx_timestamp(timestamp);

		// end of frame
		if (video_packet.size == 0)
			omx_video_buffer->nFlags |= OMX_BUFFERFLAG_ENDOFFRAME;

		// Check for changes in port settings
		if ((~flags & PORT_SETTINGS_CHANGED) && (
		    (packet_size >  0 && ilclient_remove_event   (video_decode, OMX_EventPortSettingsChanged, VIDEO_DECODE_OUT_PORT, 0, 0, 1) == 0 ) ||
		    (packet_size == 0 && ilclient_wait_for_event (video_decode, OMX_EventPortSettingsChanged, VIDEO_DECODE_OUT_PORT, 0, 0, 1, ILCLIENT_EVENT_ERROR | ILCLIENT_PARAMETER_CHANGED, 10000) == 0)))
		{
			SET_FLAG (PORT_SETTINGS_CHANGED)
			// setup tunnel between video decoder and scheduler
			if (ilclient_setup_tunnel (video_tunnel, 0, 0) != 0)
			{
				fprintf (stderr, "Error setting up tunnel between video decoder and scheduler\n");
				return 1;
			}
			ilclient_change_component_state (video_scheduler, OMX_StateExecuting);
			// setup tunnel between video scheduler and render
			if (ilclient_setup_tunnel (video_tunnel + 1, 0, 1000) != 0)
			{
				fprintf (stderr, "Error setting up tunnel between video scheduler and render\n");
				return 1;
			}

			ilclient_change_component_state (egl_render, OMX_StateIdle);
			// Enable the output port and tell egl_render to use the texture as a buffer
			//ilclient_enable_port(egl_render, EGL_RENDER_OUT_PORT); THIS BLOCKS SO CANT BE USED
			if (OMX_SendCommand (ILC_GET_HANDLE (egl_render), OMX_CommandPortEnable, EGL_RENDER_OUT_PORT, NULL) != OMX_ErrorNone)
			{
				fprintf (stderr, "OMX_CommandPortEnable failed.\n");
				return 1;
			}
			for ( int i = 0; i < BUFFER_COUNT; i++)
			{
				if (OMX_UseEGLImage (ILC_GET_HANDLE (egl_render), &omx_egl_buffers[i], EGL_RENDER_OUT_PORT, NULL, egl_images[i]) != OMX_ErrorNone)
				{
					fprintf (stderr, "OMX_UseEGLImage failed.\n");
					return 1;
				}
			}

			// Set egl_render to executing
			ilclient_change_component_state (egl_render, OMX_StateExecuting);
			// Request egl_render to write data to the texture buffer
			// *current_texture = (*current_texture + 1) % BUFFER_COUNT;
			if (OMX_FillThisBuffer (ILC_GET_HANDLE (egl_render), omx_egl_buffers[current_buffer]) != OMX_ErrorNone)
			{
				fprintf (stderr, "OMX_FillThisBuffer failed for egl buffer.\n");
				return 1;
			}
		}

		if (OMX_EmptyThisBuffer (ILC_GET_HANDLE (video_decode), omx_video_buffer) != OMX_ErrorNone)
		{
			fprintf (stderr, "Error emptying video decode buffer\n");
			return 1;
		}
		if (flags & CLOCK_PAUSED)
		{
			UNSET_FLAG(CLOCK_PAUSED);
		}
	}
	return 0;
}

/**
 *  Thread for decoding video packets.
 *  Polls the video packet buffer for new packets to decode and
 *  present on screen.
 */
static void video_decoding_thread ()
{
	uint8_t *d;
	int ret;
	while (~flags & STOPPED)
	{
		while ((~flags & DONE_READING) || (video_packet_fifo.n_packets))
		{
			// printf("DEC: Working\n");

			// check pause
			if (flags & PAUSED)
			{
				WAIT_WHILE_PAUSED
			}
			// get packet
			pthread_mutex_lock (&video_mutex);
			if ((ret = pop_packet (&video_packet_fifo, &video_packet)) != 0)
			{

				pthread_mutex_unlock (&video_mutex);
				usleep (FIFO_SLEEPY_TIME);
				continue;
			}
			// decode
			d = video_packet.data;
			ret = decode_video_packet ();
			video_packet.data = d;
			av_packet_unref (&video_packet);
			pthread_mutex_unlock (&video_mutex);
			if (ret != 0)
			{
				fprintf (stderr, "Error while decoding, ending thread\n");
				break;
			}
		}
		if ((flags & DONE_READING) && (~flags & LAST_BUFFER))
		{
			printf("DEC: --------------------- EMITTED EOS\n");
			if ((omx_video_buffer = ilclient_get_input_buffer (video_decode, VIDEO_DECODE_INPUT_PORT, 1)) != NULL)
			{
				omx_video_buffer->nFilledLen = 0;
				omx_video_buffer->nFlags 	 =  OMX_BUFFERFLAG_SYNCFRAME | OMX_BUFFERFLAG_EOS | OMX_BUFFERFLAG_DISCONTINUITY;
				if (OMX_EmptyThisBuffer (ILC_GET_HANDLE (video_decode), omx_video_buffer) != OMX_ErrorNone)
		            printf ("DEC: error emptying last buffer\n");
			}
			SET_FLAG(LAST_BUFFER);
		}
		else
		{
			// printf("DEC: Sleeping\n");
			usleep(FIFO_SLEEPY_TIME); // TODO better way of handling excessive CPU usage
		}
	}

	if (flags & STOPPED)
	{
		printf ("DEC: Flushing tunnels\n");
		ilclient_disable_port(video_decode, VIDEO_DECODE_OUT_PORT);
		ilclient_flush_tunnels        (video_tunnel, 1);
		ilclient_enable_port(video_decode, VIDEO_DECODE_OUT_PORT);
	}
	printf("DEC: --------------------- EMITTED EOS\n");

	if ((omx_video_buffer = ilclient_get_input_buffer (video_decode, VIDEO_DECODE_INPUT_PORT, 1)) != NULL)
	{
		omx_video_buffer->nFilledLen = 0;
		omx_video_buffer->nFlags 	 =  OMX_BUFFERFLAG_SYNCFRAME | OMX_BUFFERFLAG_EOS | OMX_BUFFERFLAG_DISCONTINUITY;
		if (OMX_EmptyThisBuffer (ILC_GET_HANDLE (video_decode), omx_video_buffer) != OMX_ErrorNone)
            printf ("DEC: error emptying last buffer\n");
	}
	printf ("DEC: stopping thread\n");
}


static inline int process_packet ()
{
	int ret = 0;
	packet_buffer* buf = NULL;
	// negative size ???
	if (av_packet.size < 0)
		return ret;

	// current packet is video
	if (av_packet.stream_index == video_stream_idx)
	{
		buf = &video_packet_fifo;
	}
	else
		return ret;

	// the buffer might be full therefor we need to keep trying until there room has been
	// made by either decoding threads, hence the while loop
	while (~flags & STOPPED)
	{
		if (flags & PAUSED)
		WAIT_WHILE_PAUSED
		ret = push_packet (buf, av_packet);
		// if we successfully added the packet break
		if (ret == 0)
			break;
		// sleep a little to save CPU
		usleep (FIFO_SLEEPY_TIME);
	}
	return 0;
}

/**
 *	Open video.
 *	Create components and setup tunnels and buffers between them.
 *  @return int 0 on success, non-zero on failure.
 */
static int open_video ()
{
	int ret = 0;
	memset (video_tunnel, 0, sizeof (video_tunnel));

	// create video decode component
	if (ilclient_create_component (client, &video_decode, "video_decode", ILCLIENT_DISABLE_ALL_PORTS | ILCLIENT_ENABLE_INPUT_BUFFERS) != 0)
	{
		fprintf (stderr, "Error creating IL COMPONENT video decoder\n");
		ret = -14;
	}
	list[0] = video_decode;

	// create egl_render component
	if (ilclient_create_component (client, &egl_render, "egl_render", ILCLIENT_DISABLE_ALL_PORTS | ILCLIENT_ENABLE_OUTPUT_BUFFERS) != 0)
	{
		fprintf (stderr, "Error creating IL COMPONENT egl render\n");
		ret = -14;
	}
	list[2] = egl_render;

	// set nBufferCountActual to allow binding 2 textures
	OMX_PARAM_PORTDEFINITIONTYPE portFormat;
	OMX_INIT_STRUCTURE(portFormat);
	portFormat.nPortIndex = EGL_RENDER_OUT_PORT;
	OMX_GetParameter(ILC_GET_HANDLE (egl_render), OMX_IndexParamPortDefinition, &portFormat);
	portFormat.nBufferCountActual = BUFFER_COUNT;
	OMX_SetParameter(ILC_GET_HANDLE (egl_render), OMX_IndexParamPortDefinition, &portFormat);

	portFormat.nPortIndex = EGL_RENDER_INPUT_PORT;
	OMX_GetParameter(ILC_GET_HANDLE (egl_render), OMX_IndexParamPortDefinition, &portFormat);
	portFormat.nBufferCountActual = 1;
	OMX_SetParameter(ILC_GET_HANDLE (egl_render), OMX_IndexParamPortDefinition, &portFormat);


	OMX_CONFIG_PORTBOOLEANTYPE discardMode;
	OMX_INIT_STRUCTURE(discardMode);
	discardMode.nPortIndex = EGL_RENDER_INPUT_PORT;
	if (OMX_GetParameter(ILC_GET_HANDLE(egl_render), OMX_IndexParamBrcmVideoEGLRenderDiscardMode, &discardMode) != OMX_ErrorNone)
		printf("OMX_IndexParamBrcmVideoEGLRenderDiscardMode failed.\n");
	else
		printf("OMX_IndexParamBrcmVideoEGLRenderDiscardMode: %u\n", discardMode.bEnabled);
	discardMode.bEnabled = OMX_TRUE;
	if (OMX_SetParameter(ILC_GET_HANDLE(egl_render), OMX_IndexParamBrcmVideoEGLRenderDiscardMode, &discardMode) != OMX_ErrorNone)
		printf("OMX_IndexParamBrcmVideoEGLRenderDiscardMode failed.\n");
	else
		printf("OMX_IndexParamBrcmVideoEGLRenderDiscardMode: %u\n", discardMode.bEnabled);


	// create video scheduler
	if (ilclient_create_component (client, &video_scheduler, "video_scheduler", ILCLIENT_DISABLE_ALL_PORTS) != 0)
	{
		fprintf (stderr, "Error creating IL COMPONENT video scheduler\n");
		ret = -13;
	}


	portFormat.nPortIndex = VIDEO_SCHEDULER_INPUT_PORT;
	// portFormat.nBufferCountActual = 1;
	// OMX_SetParameter(ILC_GET_HANDLE (video_scheduler), OMX_IndexParamPortDefinition, &portFormat);
	OMX_GetParameter(ILC_GET_HANDLE (video_scheduler), OMX_IndexParamPortDefinition, &portFormat);
	printf("SHD IN  nBufferCountActual: %d\n", portFormat.nBufferCountActual );
	printf("SHD IN  nBufferCountMin: %d\n", portFormat.nBufferCountMin );
	printf("SHD IN  nBufferSize: %d\n", portFormat.nBufferSize );

	portFormat.nPortIndex = VIDEO_SCHEDULER_OUT_PORT;
	// portFormat.nBufferCountActual = 1;
	// OMX_SetParameter(ILC_GET_HANDLE (video_scheduler), OMX_IndexParamPortDefinition, &portFormat);
	OMX_GetParameter(ILC_GET_HANDLE (video_scheduler), OMX_IndexParamPortDefinition, &portFormat);
	printf("SHD OUT nBufferCountActual: %d\n", portFormat.nBufferCountActual );
	printf("SHD OUT nBufferCountMin: %d\n", portFormat.nBufferCountMin );
	printf("SHD OUT nBufferSize: %d\n", portFormat.nBufferSize );

	portFormat.nPortIndex = EGL_RENDER_INPUT_PORT;
	OMX_GetParameter(ILC_GET_HANDLE (egl_render), OMX_IndexParamPortDefinition, &portFormat);
	printf("EGL IN  nBufferCountActual: %d\n", portFormat.nBufferCountActual );
	printf("EGL IN  nBufferCountMin: %d\n", portFormat.nBufferCountMin );
	printf("EGL IN  nBufferSize: %d\n", portFormat.nBufferSize );

	portFormat.nPortIndex = EGL_RENDER_OUT_PORT;
	OMX_GetParameter(ILC_GET_HANDLE (egl_render), OMX_IndexParamPortDefinition, &portFormat);
	printf("EGL OUT nBufferCountActual: %d\n", portFormat.nBufferCountActual );
	printf("EGL OUT nBufferCountMin: %d\n", portFormat.nBufferCountMin );
	printf("EGL OUT nBufferSize: %d\n", portFormat.nBufferSize );

	portFormat.nPortIndex = VIDEO_DECODE_INPUT_PORT;
	// portFormat.nBufferCountActual = 2; //default 20
	// OMX_SetParameter(ILC_GET_HANDLE (video_decode), OMX_IndexParamPortDefinition, &portFormat);
	OMX_GetParameter(ILC_GET_HANDLE (video_decode), OMX_IndexParamPortDefinition, &portFormat);
	printf("DEC IN  nBufferCountActual: %d\n", portFormat.nBufferCountActual );
	printf("DEC IN  nBufferCountMin: %d\n", portFormat.nBufferCountMin );
	printf("DEC IN  nBufferSize: %d\n", portFormat.nBufferSize );

	portFormat.nPortIndex = VIDEO_DECODE_OUT_PORT;
	// portFormat.nBufferCountActual = 1; //default 20
	// OMX_SetParameter(ILC_GET_HANDLE (video_decode), OMX_IndexParamPortDefinition, &portFormat);
	OMX_GetParameter(ILC_GET_HANDLE (video_decode), OMX_IndexParamPortDefinition, &portFormat);
	printf("DEC OUT nBufferCountActual: %d\n", portFormat.nBufferCountActual );
	printf("DEC OUT nBufferCountMin: %d\n", portFormat.nBufferCountMin );
	printf("DEC OUT nBufferSize: %d\n", portFormat.nBufferSize );


	list[1] = video_scheduler;
	// setup tunnels
	set_tunnel (video_tunnel, 		video_decode, 		 VIDEO_DECODE_OUT_PORT, 	video_scheduler, 	VIDEO_SCHEDULER_INPUT_PORT);
	set_tunnel (video_tunnel + 1, 	video_scheduler, 	 VIDEO_SCHEDULER_OUT_PORT,  egl_render, 		EGL_RENDER_INPUT_PORT);
	set_tunnel (video_tunnel + 2, 	video_clock, 		 CLOCK_VIDEO_PORT, 			video_scheduler, 	VIDEO_SCHEDULER_CLOCK_PORT);
	// setup clock tunnel
	if (ilclient_setup_tunnel (video_tunnel + 2, 0, 0) != 0)
	{
		fprintf (stderr, "Error setting up tunnel\n");
		ret = -15;
	}
	// setup decoding
	if (ret == 0)
		ilclient_change_component_state (video_decode, OMX_StateIdle);

	OMX_VIDEO_PARAM_PORTFORMATTYPE video_format;
	OMX_INIT_STRUCTURE(video_format);
	video_format.nPortIndex 		 = VIDEO_DECODE_INPUT_PORT;

	if (video_stream->r_frame_rate.den > 0)
		video_format.xFramerate	= (long long) (video_stream->r_frame_rate.num / video_stream->r_frame_rate.den) * (1 << 16);

	printf("FRAME RATE NUM: %d\n", video_stream->r_frame_rate.num );
	printf("FRAME RATE DEN: %d\n", video_stream->r_frame_rate.den );
	printf("AVG F RATE NUM: %d\n", video_stream->avg_frame_rate.num );
	printf("AVG F RATE DEN: %d\n", video_stream->avg_frame_rate.den );
	printf("FRAME RATE: %d\n", video_format.xFramerate );


	switch (video_codec_ctx->codec_id)
	{
		case AV_CODEC_ID_H264:
			video_format.eCompressionFormat = OMX_VIDEO_CodingAVC;
			break;

		case AV_CODEC_ID_MPEG4:
			video_format.eCompressionFormat = OMX_VIDEO_CodingMPEG4;
			break;

		case AV_CODEC_ID_MPEG2VIDEO:
			video_format.eCompressionFormat = OMX_VIDEO_CodingMPEG2;
			break;

		default:
			video_format.eCompressionFormat = OMX_VIDEO_CodingAutoDetect;
			break;
	}
	// set format parameters for video decoder
	if (OMX_SetParameter (ILC_GET_HANDLE (video_decode), OMX_IndexParamVideoPortFormat, &video_format) != OMX_ErrorNone)
	{
		fprintf (stderr, "Error setting port format parameter on video decoder \n");
		return 1;
	}
	// enable video decoder buffers
	if (ilclient_enable_port_buffers (video_decode, VIDEO_DECODE_INPUT_PORT, NULL, NULL, NULL) == 0)
	{
		ilclient_change_component_state (video_decode, OMX_StateExecuting);
		// send decoding extra information
		if (video_codec_ctx->extradata)
		{
			if ((omx_video_buffer = ilclient_get_input_buffer (video_decode, VIDEO_DECODE_INPUT_PORT, 1)) == NULL)
			{
				fprintf (stderr, "Error getting input buffer to video decoder to send decoding information\n");
				return 1;
			}
			omx_video_buffer->nOffset = 0;
			omx_video_buffer->nFilledLen = video_codec_ctx->extradata_size;
			memset (omx_video_buffer->pBuffer, 0x0, omx_video_buffer->nAllocLen);
			memcpy (omx_video_buffer->pBuffer, video_codec_ctx->extradata, video_codec_ctx->extradata_size);
			omx_video_buffer->nFlags = OMX_BUFFERFLAG_CODECCONFIG | OMX_BUFFERFLAG_ENDOFFRAME;

			if (OMX_EmptyThisBuffer (ILC_GET_HANDLE (video_decode), omx_video_buffer) != OMX_ErrorNone)
			{
				fprintf (stderr, "Error emptying buffer with extra decoder information\n");
				return 1;
			}
		}
	}
	else
	{
		fprintf (stderr, "Could not enable port buffers on video decoder\n");
		return 1;
	}
	return 0;
}

/**
 *	Close video
 * 	Destroy components and tunnels between them,
 */
static void close_video ()
{
	if ((omx_video_buffer = ilclient_get_input_buffer (video_decode, VIDEO_DECODE_INPUT_PORT, 1)) != NULL)
	{
		omx_video_buffer->nFilledLen = 0;
		omx_video_buffer->nFlags 	 =  OMX_BUFFERFLAG_EOS | OMX_BUFFERFLAG_TIME_UNKNOWN;
		if (OMX_EmptyThisBuffer (ILC_GET_HANDLE (video_decode), omx_video_buffer) != OMX_ErrorNone)
            fprintf (stderr, "error emptying last buffer =/\n");
	}
	else
        fprintf (stderr, "Could not send EOS flag to video decoder\n");

	// wait for EOS from render
	printf("VID: Waiting for EOS from render\n");
	ilclient_wait_for_event(video_decode, OMX_EventBufferFlag, VIDEO_DECODE_OUT_PORT, 0, 0, 1, ILCLIENT_BUFFER_FLAG_EOS, 10000);

	// need to flush the renderer to allow video_decode to disable its input port
	printf("VID: Flushing tunnels\n");
	ilclient_flush_tunnels        (video_tunnel, 0);
	printf("VID: Disabling port buffers\n");
	ilclient_disable_port_buffers (video_decode, VIDEO_DECODE_INPUT_PORT, NULL, NULL, NULL);
	ilclient_disable_port_buffers (video_decode, VIDEO_DECODE_OUT_PORT, NULL, NULL, NULL);
	ilclient_disable_tunnel       (video_tunnel);
	ilclient_disable_tunnel       (video_tunnel + 1);
	ilclient_disable_tunnel       (video_tunnel + 2);
	ilclient_teardown_tunnels     (video_tunnel);
	if (video_codec_ctx)
        avcodec_close (video_codec_ctx);
    fprintf (stderr, "VID: Cleanup completed.\n");
}


static int open_codec_context (int* stream_idx, enum AVMediaType type)
{
	int 			ret;
	AVStream* 	    stream;
	AVCodecContext* codec_ctx 	= NULL;
	AVCodec* 	    dec 		= NULL;

	ret = av_find_best_stream (fmt_ctx, type, -1, -1, &dec, 0);
	*stream_idx = ret;
	printf("STREAM IDX: %i\n", ret);
	if (ret < 0)
	{
		fprintf (stderr, "Could not find %s stream in input file\n", type == AVMEDIA_TYPE_VIDEO ? "video" : "audio");
		return ret;
	}

	stream    = fmt_ctx->streams[*stream_idx];
	codec_ctx = stream->codec;
	codec_ctx->workaround_bugs = FF_BUG_AUTODETECT;
	codec_ctx->thread_count=1;

	printf("codec->codec_id %i\n", dec->id);


	if (!dec)
	{
		fprintf (stderr, "Failed to find %s codec\n", type == AVMEDIA_TYPE_VIDEO ? "video" : "audio");
		return 1;
	}
	if ((ret = avcodec_open2 (codec_ctx, dec, NULL)) < 0)
	{
		fprintf (stderr, "Failed to open %s codec\n", type == AVMEDIA_TYPE_VIDEO ? "video" : "audio");
		return ret;
	}
	printf("codec_ctx->width: %i\n", codec_ctx->width);
	printf("codec_ctx->height: %i\n", codec_ctx->height);
	return 0;
}


static int create_hw_clock ()
{
	int ret = 0;
	// create clock
	if (ilclient_create_component (client, &video_clock, "clock", ILCLIENT_DISABLE_ALL_PORTS) != 0)
	{
		fprintf (stderr, "Error creating IL COMPONENT video clock\n");
		ret = -14;
	}
	if (video_clock == NULL)
		fprintf (stderr, "Error?\n");

	list[3] = video_clock;

	return ret;
}


static void cleanup ()
{
	destroy_packet_buffer (&video_packet_fifo);

	if (video_stream_idx != AVERROR_STREAM_NOT_FOUND)
	{
		close_video ();
		printf ("     video closed\n");
	}

	printf ("  freeing ffmpeg structs\n");
	av_frame_free (&av_frame);
	avformat_close_input (&fmt_ctx);

	printf ("  cleaning up %i components\n", sizeof(list)/sizeof(list[0]) );
	// for ( int i = 0; i < sizeof(list)/sizeof(list[0]); i++)
	// 	printf("%p\n", list[i]);

	ilclient_state_transition   (list, OMX_StateIdle);
	printf ("  OMX_StateIdle OK\n");

	ilclient_cleanup_components (list);
	printf ("  ilclient_cleanup_components OK\n");

	flags = 0;
	printf ("  Cleanup up completed\n");
}


uint64_t rpi_mp_current_time ()
{
	OMX_TIME_CONFIG_TIMESTAMPTYPE timestamp;
	OMX_INIT_STRUCTURE(timestamp);
	timestamp.nPortIndex		= CLOCK_VIDEO_PORT;

	OMX_ERRORTYPE omx_error;
	if (( omx_error = OMX_GetParameter (ILC_GET_HANDLE (video_clock), OMX_IndexConfigTimeCurrentMediaTime, &timestamp)) != OMX_ErrorNone)
	{
		fprintf (stderr, "Could not get timestamp config from clock component. Error 0x%08x\n", omx_error);
		return 0;
	}
	uint64_t pts = (uint64_t) (timestamp.nTimestamp.nLowPart | (uint64_t) timestamp.nTimestamp.nHighPart << 32);
	return pts / AV_TIME_BASE;
}


// TODO implement correctly
int rpi_mp_seek (int64_t position)
{
	printf ( "SEEK: Trying to rewind\n" );

	lock();

	OMX_TIME_CONFIG_CLOCKSTATETYPE clock;
	OMX_INIT_STRUCTURE(clock);
	clock.eState    		= OMX_TIME_ClockStateStopped;

	if ( OMX_SetParameter ( ILC_GET_HANDLE ( video_clock ), OMX_IndexConfigTimeClockState, & clock ) != OMX_ErrorNone )
	{
		printf ("SEEK: Could not stop clock\n");
	 	return 0;
	}

	SET_FLAG(CLOCK_PAUSED);

	// seek to frame
	int ret = av_seek_frame ( fmt_ctx, -1, 0, AVSEEK_FLAG_FRAME | AVSEEK_FLAG_BACKWARD );

	printf ("SEEK: Flushing FIFO\n");
    flush_buffer ( & video_packet_fifo );

	ilclient_disable_port(video_decode, VIDEO_DECODE_OUT_PORT);
	ilclient_flush_tunnels        (video_tunnel, 1);
	ilclient_enable_port(video_decode, VIDEO_DECODE_OUT_PORT);

	// flush video buffer
	printf ("SEEK: Flushing video_decode INPUT\n");
	if ( OMX_SendCommand ( ILC_GET_HANDLE ( video_decode ), OMX_CommandFlush, VIDEO_DECODE_INPUT_PORT, NULL ) != OMX_ErrorNone )
		printf ("SEEK: Could not flush video decoder input\n");

	printf ("SEEK: Flushing video_codec_ctx\n");
	avcodec_flush_buffers ( video_codec_ctx );

	SET_FLAG ( FIRST_VIDEO );
	unlock();
	setup_clock();

	if (ret < 0)
		printf ("SEEK: Could not rewind video\n");
	return ret;
}


int rpi_mp_init ()
{

	//get refresh rate of the monitor
	TV_DISPLAY_STATE_T display_state;
	memset(&display_state, 0, sizeof(TV_DISPLAY_STATE_T));
	vc_tv_get_display_state(&display_state);
	if(display_state.state & ( VC_HDMI_HDMI | VC_HDMI_DVI ))
		refresh_rate = display_state.display.hdmi.frame_rate;
	else
		refresh_rate = display_state.display.sdtv.frame_rate;

	printf("REFRESH RATE: %d\n", refresh_rate );

	av_register_all ();
	avformat_network_init ();
	// init IL client lib
	if ((client = ilclient_init ()) == NULL)
	{
		fprintf (stderr, "Could not init ilclient\n");
		return -1;
	}
	// init OMX
	if (OMX_Init () != OMX_ErrorNone)
	{
		fprintf (stderr, "Could not init OMX, aborting\n");
		ilclient_destroy (client);
		return 1;
	}
	memset (list, 0, sizeof (list));
	return 0;
}


void rpi_mp_deinit ()
{
	OMX_Deinit();
	ilclient_destroy (client);
}


int rpi_mp_open (const char* source, int* image_width, int* image_height, int64_t* duration, int init_flags)
{
	int ret = 0;
	flags = FIRST_VIDEO |
			(init_flags & LOOP ? LOOP_VIDEO : 0);

	// egl callback
	ilclient_set_fill_buffer_done_callback (client, fill_egl_texture_buffer, 0);

    // open source
	if (avformat_open_input (&fmt_ctx, source, NULL, NULL) < 0)
	{
		fprintf (stderr, "Could not open source %s\n", source);
		return 1;
	}
    // search for streams
	if (avformat_find_stream_info (fmt_ctx, NULL) < 0)
	{
		fprintf (stderr, "Could not find stream information\n");
		return 1;
	}
	// create clock
	if (create_hw_clock() == 0)
	{
		// open video
		if (open_codec_context (&video_stream_idx, AVMEDIA_TYPE_VIDEO) == 0)
		{
			video_stream    = fmt_ctx->streams[video_stream_idx];
			video_codec_ctx = video_stream->codec;

			if (open_video() == 0)
			{
				*image_width  = video_codec_ctx->width;
				*image_height = video_codec_ctx->height;
			}
		}

		// check that we did get streams
		if (video_stream_idx == AVERROR_STREAM_NOT_FOUND)
		{
			fprintf (stderr, "Could not find video in input, aborting\n");
			ret = 1;
			goto end;
		}


		video_duration = (video_stream->duration * video_stream->time_base.num * AV_TIME_BASE) / video_stream->time_base.den;
		printf("VIDEO DURATION: %i\n", video_duration );
		printf("video_stream->duration: %lli\n", video_stream->duration );
		printf("video_stream->time_base.num: %i\n", video_stream->time_base.num );
		printf("video_stream->time_base.den: %i\n", video_stream->time_base.den );

		*duration = fmt_ctx->duration / AV_TIME_BASE;

		if (setup_clock() != 0)
		{
			fprintf (stderr, "Could not setup HW clock\n");
			ret = 1;
			goto end;
		}
	}
	else
	{
		fprintf (stderr, "Could not create clock. exiting\n");
		return 1;
	}

	// allocate frame for decoding (audio here)
	if (!(av_frame = av_frame_alloc()))
	{
		fprintf (stderr, "Could not allocate frame\n");
		ret = AVERROR (ENOMEM);
		goto end;
	}
	// initialize packet
	av_init_packet (&av_packet);
	av_packet.data = NULL;
	av_packet.size = 0;

	// init buffers
	init_packet_buffer (&video_packet_fifo, 1024 * 1024 * 5);
end:
	return ret;
}


void rpi_mp_setup_render_buffer (void *_egl_images[], int *_current_texture, pthread_mutex_t** draw_mutex, pthread_cond_t** draw_cond)
{
	for ( int i = 0; i < BUFFER_COUNT; i++)
		egl_images[i] = _egl_images[i];

	current_texture = _current_texture;
	*draw_mutex = &buffer_filled_mut;
	*draw_cond  = &buffer_filled_cond;
}


int rpi_mp_start ()
{

	OMX_TIME_CONFIG_ACTIVEREFCLOCKTYPE reference_clock;
	OMX_INIT_STRUCTURE(reference_clock);
	reference_clock.eClock = OMX_TIME_RefClockVideo;
	if( OMX_SetConfig(ILC_GET_HANDLE(video_clock), OMX_IndexConfigTimeActiveRefClock, &reference_clock) != OMX_ErrorNone)
		fprintf (stderr, "---------------OMX_IndexConfigTimeActiveRefClock failed.\n");

	// start threads
	pthread_t video_decoding;
	pthread_create (&video_decoding, NULL, (void*) &video_decoding_thread, NULL);

	// start clock
	ilclient_change_component_state (video_clock, OMX_StateExecuting);


	while (1)
	{
		printf("PAC:-read_packets_thread\n");
		// read packets from source
		while ((~flags & STOPPED) && (~flags & DONE_READING))
		{
			if (av_read_frame (fmt_ctx, &av_packet) >= 0)
			{
				if (process_packet() != 0)
				{
					printf("PAC:---------process_packet 0\n");
					break;
				}
			}
			else
			{
				printf("PAC:---------done_reading\n");
				SET_FLAG (DONE_READING);
			}
			usleep(100); // TODO: FINDA A BETTER WAY OF REDUCING CPU USAGE
		}

		printf("PAC:-waiting for EOS\n");
		ilclient_wait_for_event(egl_render, OMX_EventBufferFlag, EGL_RENDER_OUT_PORT, 0, 0, 1, ILCLIENT_BUFFER_FLAG_EOS, 15000);
		printf("PAC:-received EOS\n");

		SET_FLAG(LAST_FRAME);

		if ((~flags & LOOP_VIDEO) || (flags & STOPPED))
		{
			printf("PAC:---end---\n");
			break;
		}

		if (flags & LAST_FRAME)
		{
			printf("PAC:---av_seek_frame---\n");
			rpi_mp_seek (0);
			UNSET_FLAG (DONE_READING);
			UNSET_FLAG (LAST_BUFFER);
			UNSET_FLAG (LAST_FRAME);
		}
		else
		{
			printf("PAC: Sleeping\n");
			usleep(FIFO_SLEEPY_TIME);
		}
	}

	SET_FLAG (DONE_READING);
	printf ("done reading\n");

	// wait for all threads to end
	SET_FLAG (STOPPED); //TU CIE MAM
	printf("-waiting for video thread\n");
	pthread_join (video_decoding, NULL);
	printf("-finished video thread\n");

	// cleanup
	printf ("cleaning up... \n");
	cleanup ();
	printf ("stopping reading thread\n");
	return 0;
}


void rpi_mp_stop ()
{
	SET_FLAG (STOPPED);

	// make sure to unpause otherwise threads won't exit
	if (flags & PAUSED)
        rpi_mp_pause();

    SET_FLAG (DONE_READING);
    flush_buffer ( & video_packet_fifo );

	// flush video component
	if (video_stream_idx != AVERROR_STREAM_NOT_FOUND)
	{
		OMX_ERRORTYPE omx_error;
		if ((omx_error = OMX_SendCommand (ILC_GET_HANDLE (video_decode), OMX_CommandFlush, VIDEO_DECODE_INPUT_PORT, NULL) != OMX_ErrorNone))
			fprintf (stderr, "Could not flush video decoder input (0x%08x)\n", omx_error);
	}
}


void rpi_mp_pause ()
{
	OMX_TIME_CONFIG_SCALETYPE scale;
	OMX_INIT_STRUCTURE(scale);
	scale.xScale 			= (~flags & PAUSED ? 0 : 1 << 16);

	OMX_ERRORTYPE omx_error;
	if ((omx_error = OMX_SetParameter (ILC_GET_HANDLE (video_clock), OMX_IndexConfigTimeScale, &scale)) != OMX_ErrorNone)
	{
		fprintf (stderr, "Could not set scale parameter on video clock. Error 0x%08x\n", omx_error);
		return;
	}

	if (~flags & PAUSED)
	{
		SET_FLAG (PAUSED);

		OMX_ERRORTYPE omx_error;

		// TODO: is this neccessary?
		OMX_TIME_CONFIG_TIMESTAMPTYPE timestamp;
		OMX_INIT_STRUCTURE(timestamp);

		timestamp.nPortIndex		= CLOCK_VIDEO_PORT;
		if (( omx_error = OMX_GetParameter (ILC_GET_HANDLE (video_clock), OMX_IndexConfigTimeCurrentMediaTime, &timestamp)) != OMX_ErrorNone)
		{
			fprintf (stderr, "Could not get timestamp config from clock component. Error 0x%08x\n", omx_error);
		}
		else
		{
			uint64_t pts = (uint64_t) (timestamp.nTimestamp.nLowPart | (uint64_t) timestamp.nTimestamp.nHighPart << 32);
			printf("OMX_IndexConfigTimeCurrentMediaTime VIDEO: %llu\n", pts * 1000000LL / (uint64_t)AV_TIME_BASE);
		}
		printf("PAUSED\n");
	}
	else
	{
		UNSET_FLAG (PAUSED);
		pthread_cond_broadcast (&pause_condition);
		printf("PLAYING\n");
	}
}

int rpi_mp_metadata (const char* key, char** title)
{
	AVDictionaryEntry* entry = NULL;
	entry = av_dict_get (fmt_ctx->metadata, key, 0, AV_DICT_IGNORE_SUFFIX);
	if (!entry)
		return 1;
	*title = entry->value;
	return 0;
}
