#include "rpi_mp.h"
#include <stdio.h>
#include <pthread.h>
#include <stdlib.h>
#include "GLES/gl.h"
#include "EGL/egl.h"
#include "EGL/eglext.h"
#include <assert.h>
#include "bcm_host.h"
#include <math.h>
#include "rpi_mp_utils.h"


#ifndef M_PI
	#define M_PI 3.141592654
#endif

static int done = 0;
static pthread_t input_listener;
static pthread_t egl_draw;
static EGLDisplay display;
static EGLSurface surface;
static EGLContext context;
static uint32_t screen_width;
static uint32_t screen_height;
static int64_t duration;

static GLuint textures[BUFFER_COUNT];
void  *egl_images[BUFFER_COUNT];
static int current_texture = 0;

static pthread_mutex_t* texture_ready_mut;
static pthread_cond_t* texture_ready_cond;

int image_width, image_height;
int flags;

char * source;

static int layer = 0;

/** Texture coordinates for the quad. */
static const GLfloat tex_coords[6 * 4 * 2] = {
	0.f,  1.f,
	1.f,  1.f,
	0.f,  0.f,
	1.f,  0.f,

	0.f,  0.f,
	1.f,  0.f,
	0.f,  1.f,
	1.f,  1.f,

	0.f,  0.f,
	1.f,  0.f,
	0.f,  1.f,
	1.f,  1.f,

	0.f,  0.f,
	1.f,  0.f,
	0.f,  1.f,
	1.f,  1.f,

	0.f,  0.f,
	1.f,  0.f,
	0.f,  1.f,
	1.f,  1.f,

	0.f,  0.f,
	1.f,  0.f,
	0.f,  1.f,
	1.f,  1.f,
};

static const GLbyte quadx[6*4*3] = {
	/* FRONT */
	-15, -10,  10,
	15, -10,  10,
	-15,  10,  10,
	15,  10,  10,

	/* BACK */
	-10, -10, -10,
	-10,  10, -10,
	10, -10, -10,
	10,  10, -10,

	/* LEFT */
	-10, -10,  10,
	-10,  10,  10,
	-10, -10, -10,
	-10,  10, -10,

	/* RIGHT */
	10, -10, -10,
	10,  10, -10,
	10, -10,  10,
	10,  10,  10,

	/* TOP */
	-10,  10,  10,
	10,  10,  10,
	-10,  10, -10,
	10,  10, -10,

	/* BOTTOM */
	-10, -10,  10,
	-10, -10, -10,
	10, -10,  10,
	10, -10, -10,
};


static void* listen_stdin (void* thread_id)
{
	char command;
	char* title;
	uint64_t t;
	// read input from stdin
	printf (">> ");
	while (!done)
	{
		command = getc (stdin);
		switch (command)
		{
			case ' ':
				rpi_mp_pause ();
				break;

			case 's':
				rpi_mp_stop ();
				done = 1;
				break;

				case 'q':
				done = 1;
				break;

				case 'n':
					 rpi_mp_seek (rpi_mp_current_time() + 180);
					break;

				case 'p':
					rpi_mp_seek (rpi_mp_current_time() - 60);
					break;

				case 't':
					t = rpi_mp_current_time();
					printf ("current time is : %.2d:%.2d:%.2d\n", (int) t / 3600, (int) (t % 3600) / 60, (int) t % 60);
					break;

				case 'a':
					if (rpi_mp_metadata ("StreamTitle", &title) == 0)
						  printf ("title: %s\n", title);
					else
						  printf ("no title ...\n");
					break;

				case '\n':
					 /* ignore */
					continue;
					break;

				default:
					printf ("\n");
					break;
		}
		printf (">> ");
	}
	printf ("\n");
	return NULL;
}

static void init_textures ()
{
	// the textures containing the video frames
	glGenTextures ( BUFFER_COUNT, &textures[0] );

	for ( int i = 0; i < BUFFER_COUNT; i++ )
	{
		glBindTexture ( GL_TEXTURE_2D, textures[i] );
		glTexImage2D  ( GL_TEXTURE_2D, 0, GL_RGBA, image_width, image_height, 0, GL_RGBA, GL_UNSIGNED_BYTE, NULL );

		glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
		glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
		glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
		glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);

		egl_images[i] = eglCreateImageKHR ( display,
										context,
										EGL_GL_TEXTURE_2D_KHR,
										(EGLClientBuffer) textures[i],
										0 );
	}

	// setup overall texture environment
	glTexCoordPointer(2, GL_FLOAT, 0, tex_coords);
	glEnableClientState(GL_TEXTURE_COORD_ARRAY);

	glEnable(GL_TEXTURE_2D);

	// Bind texture surface to current vertices
	glBindTexture(GL_TEXTURE_2D, textures[current_texture]);
}


/***********************************************************
 * Name: init_ogl
 *
 * Arguments:
 *       CUBE_STATE_T *state - holds OGLES model info
 *
 * Description: Sets the display, OpenGL|ES context and screen stuff
 *
 * Returns: void
 *
 ***********************************************************/
static void init_ogl ()
{
	int32_t success = 0;
	EGLBoolean result;
	EGLint num_config;

	static EGL_DISPMANX_WINDOW_T nativewindow;

	DISPMANX_ELEMENT_HANDLE_T dispman_element;
	DISPMANX_DISPLAY_HANDLE_T dispman_display;
	DISPMANX_UPDATE_HANDLE_T dispman_update;
	VC_RECT_T dst_rect;
	VC_RECT_T src_rect;

	static const EGLint attribute_list[] =
	{
		EGL_RED_SIZE, 8,
		EGL_GREEN_SIZE, 8,
		EGL_BLUE_SIZE, 8,
		EGL_ALPHA_SIZE, 8,
		EGL_DEPTH_SIZE, 16,
		EGL_SAMPLES, 4,
		EGL_SURFACE_TYPE, EGL_WINDOW_BIT,
		EGL_NONE
	};

	EGLConfig config;

	// get an EGL display connection
	display = eglGetDisplay(EGL_DEFAULT_DISPLAY);
	assert(display!=EGL_NO_DISPLAY);

	// initialize the EGL display connection
	result = eglInitialize(display, NULL, NULL);
	assert(EGL_FALSE != result);

	// get an appropriate EGL frame buffer configuration
	// this uses a BRCM extension that gets the closest match, rather than standard which returns anything that matches
	result = eglSaneChooseConfigBRCM(display, attribute_list, &config, 1, &num_config);
	assert(EGL_FALSE != result);

	// create an EGL rendering context
	context = eglCreateContext(display, config, EGL_NO_CONTEXT, NULL);
	assert(context!=EGL_NO_CONTEXT);

	// create an EGL window surface
	success = graphics_get_display_size(0 /* LCD */, & screen_width, & screen_height);
	assert( success >= 0 );

	dst_rect.x = 0;
	dst_rect.y = 0;
	dst_rect.width = screen_width;
	dst_rect.height = screen_height;

	src_rect.x = 0;
	src_rect.y = 0;
	src_rect.width = screen_width << 16;
	src_rect.height = screen_height << 16;

	dispman_display = vc_dispmanx_display_open( 0 /* LCD */);
	dispman_update = vc_dispmanx_update_start( 0 );

	printf("dispmanx layer: %d\n", layer);
	dispman_element = vc_dispmanx_element_add ( dispman_update, dispman_display,
		layer/*layer*/, &dst_rect, 0/*src*/,
		&src_rect, DISPMANX_PROTECTION_NONE, 0 /*alpha*/, 0/*clamp*/, 0/*transform*/);

	nativewindow.element = dispman_element;
	nativewindow.width = screen_width;
	nativewindow.height = screen_height;
	vc_dispmanx_update_submit_sync( dispman_update );

	surface = eglCreateWindowSurface( display, config, &nativewindow, NULL );
	assert(surface != EGL_NO_SURFACE);

	// connect the context to the surface
	result = eglMakeCurrent(display, surface, surface, context);
	assert(EGL_FALSE != result);

	// Set background color and clear buffers
	glClearColor (0.1f, 0.1f, 0.1f, 1.0f);

	// Enable back face culling.
	//glEnable (GL_CULL_FACE);


	float nearp = 1.0f;
	float farp = 500.0f;
	float hht = nearp * (float)tan(45.0 / 2.0 / 180.0 * M_PI);
	float hwd = hht * (float) screen_width / (float) screen_height;

	glViewport(0, 0, (GLsizei) screen_width, (GLsizei) screen_height);
	glMatrixMode(GL_PROJECTION);
	glLoadIdentity();

	glFrustumf(-hwd, hwd, -hht, hht, nearp, farp);

	glEnableClientState( GL_VERTEX_ARRAY );
	glVertexPointer( 3, GL_BYTE, 0, quadx );
}


static void destroy_function ()
{
	if (egl_images[0] != 0)
	{
		printf ("EGL destroy\n");
		for ( int i = 0; i < BUFFER_COUNT; i++)
		{
			if (!eglDestroyImageKHR (display, (EGLImageKHR) egl_images[i]))
				fprintf (stderr, "eglDestroyImageKHR failed.");
		}
		// clear screen
		glClear           (GL_COLOR_BUFFER_BIT);
		eglSwapBuffers    (display, surface);
		// Release OpenGL resources
		eglMakeCurrent    (display, EGL_NO_SURFACE, EGL_NO_SURFACE, EGL_NO_CONTEXT);
		eglDestroySurface (display, surface);
		eglDestroyContext (display, context);
		eglTerminate      (display);
	}
	rpi_mp_deinit ();
}

// animating zoom level to make tearing visible by uncoupling video decoder and opengl renderer
float zoom = -34.f;
int busy_wait = 0;

static void draw ()
{
	// simulating the CPU load
	busy_wait += 50;
	if (busy_wait > 10000) busy_wait = 0;
	usleep(busy_wait);

	glClear        (GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
	glBindTexture ( GL_TEXTURE_2D, textures[(current_texture + 1) % BUFFER_COUNT] );
	glMatrixMode   (GL_MODELVIEW);
	glLoadIdentity ();
	glTranslatef   (0.f, 0.f, zoom);
	zoom -= 0.005;
	glDrawArrays   (GL_TRIANGLE_STRIP, 0, 4);

	eglSwapBuffers (display, surface);
}


static void* play_video ()
{
	rpi_mp_start ();
	done = 1;
	return NULL;
}


static int check_arguments (int argc, char** argv)
{
	flags = 0;
	int i;

	if (argc < 2)
	{
		printf ("Usage: \n%s [texture] [analog-audio] <source>\n", argv[0]);
		return 1;
	}

	for (i = 0; i < argc; i ++)
	{
		if (strcmp (argv[i], "texture") == 0)
			flags |= RENDER_VIDEO_TO_TEXTURE;
		else if (strcmp (argv[i], "analog-audio") == 0)
			flags |= ANALOG_AUDIO;
		else if (strcmp (argv[i], "layer") == 0)
			layer = atoi(argv[i+1]);
	}
	return 0;
}


int main (int argc, char** argv)
{
	// this switches egl window from triple to double buffering
	// setenv("V3D_DOUBLE_BUFFER", "1", 1);

	if (check_arguments (argc, argv))
		return 1;
	bcm_host_init ();


	if (rpi_mp_init () || rpi_mp_open (argv[argc - 1],
		&image_width,
		&image_height,
		&duration,
		flags))
		return 1;

	if (flags & RENDER_VIDEO_TO_TEXTURE)
	{
		init_ogl();
		init_textures();
		rpi_mp_setup_render_buffer (egl_images, &current_texture, &texture_ready_mut, &texture_ready_cond);
	}

	pthread_create (&egl_draw,       NULL, &play_video,   NULL);
	pthread_create (&input_listener, NULL, &listen_stdin, NULL);

	if (flags & RENDER_VIDEO_TO_TEXTURE)
		while (!done)
			draw ();
	printf("Draw loop finished\n");
	pthread_cancel (input_listener );
	printf("input_listener finished\n");
	pthread_join (egl_draw, NULL);
	printf("egl_draw finished\n");
	destroy_function ();
	printf("destroy finished\n");
	return 0;
}
