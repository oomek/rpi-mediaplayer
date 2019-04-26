#include "rpi_mp_packet_buffer.h"
#include "rpi_mp_utils.h"

#define FIFO_ALLOC_SIZE 10000
#define SORTED_PACKETS 5

// static sorted_packets         sorted_packets_table[SORTED_PACKETS];

static inline int64_t int64_timestamp (AVFormatContext* fmt_ctx, AVPacket *p)
{
	int64_t pts = p->pts != AV_NOPTS_VALUE ? p->pts : p->dts != AV_NOPTS_VALUE ? p->dts : 0;
	int64_t      num = fmt_ctx->streams[p->stream_index]->time_base.num;
	int64_t      den = fmt_ctx->streams[p->stream_index]->time_base.den;

	return ( pts * num * AV_TIME_BASE ) / den;
}

int init_packet_buffer (packet_buffer* buffer, uint size)
{
	buffer->n_packets 	= 0;
	buffer->size  		= size;
	buffer->capacity	= FIFO_ALLOC_SIZE;
	buffer->packets 	= (AVPacket*) malloc (FIFO_ALLOC_SIZE * sizeof (AVPacket));
	pthread_mutex_init (&buffer->mutex, NULL);

	// buffer->preload     = 0;
	// for (int i = 0; i < SORTED_PACKETS; i++)
	// {
	// 	sorted_packets_table[i].filled = 0;
	// 	sorted_packets_table[i].timestamp = 0LL;
	// 	sorted_packets_table[i].packet = av_packet_alloc();
	// }

	// error
	if (!buffer->packets)
		return 1;

	memset (buffer->packets, 0x0, FIFO_ALLOC_SIZE * sizeof (AVPacket));
	buffer->_front = buffer->_back = buffer->packets;
	return 0;
}


void destroy_packet_buffer (packet_buffer* buffer)
{
	flush_buffer (buffer);
	free (buffer->packets);
	buffer->n_packets = 0;
	buffer->size 	  = 0;
	buffer->preload   = 0;
	pthread_mutex_destroy (&buffer->mutex);
}


int push_packet (packet_buffer* buffer, AVPacket* p)
{
	pthread_mutex_lock (&buffer->mutex);
	int ret = 0;
	// check if size would be too large
	if (buffer->size_packets + p->size > buffer->size)
	{
		ret = FULL_BUFFER;
		goto end;
	}
	// we might need to increment the size of the allocated buffer
	if (buffer->n_packets == buffer->capacity - 1)
	{
		// allocate new larger buffer
		printf("Allocate new larger buffer\n");
		AVPacket* tmp = (AVPacket*) malloc (sizeof (AVPacket) * (buffer->capacity + FIFO_ALLOC_SIZE));
		memset (tmp, 0x0, sizeof (AVPacket) * (buffer->capacity + FIFO_ALLOC_SIZE));
		// copy packets
		if (buffer->_front < buffer->_back)
			memcpy (tmp, buffer->_front, sizeof (AVPacket) * (buffer->n_packets - 1));
		else
		{
			int n = buffer->capacity - (buffer->_front - buffer->packets);
			memcpy (tmp,     buffer->_front,  sizeof (AVPacket) * n);
			memcpy (tmp + n, buffer->packets, sizeof (AVPacket) * (buffer->n_packets - n));
		}
		// free old buffer and set pointers
		free (buffer->packets);
		buffer->capacity += FIFO_ALLOC_SIZE;
		buffer->packets = tmp;
		buffer->_front = buffer->packets;
		buffer->_back  = buffer->packets + buffer->n_packets;
	}
	*buffer->_back = *p;
	buffer->n_packets ++;
	buffer->_back ++;
	buffer->size_packets += p->size;
	// loop the back pointer back to the beginning of the buffer
	if (buffer->_back - buffer->packets == buffer->capacity)
		buffer->_back = buffer->packets;
end:
	pthread_mutex_unlock (&buffer->mutex);
	return ret;
}

int compare (const void * a, const void * b)
{
	sorted_packets *orderA = (sorted_packets *)a;
	sorted_packets *orderB = (sorted_packets *)b;

	// printf("%lli %lli \n", orderB->timestamp, orderA->timestamp);
	if ( orderA->timestamp > orderB->timestamp ) return 1;
	// if ( orderA->timestamp == orderB->timestamp ) return 0;
	// if ( orderA->timestamp >  orderB->timestamp ) return -1;
	// return ( orderA->timestamp - orderB->timestamp );
	return 0;
}

int pop_packet (packet_buffer* buffer, AVFormatContext* fmt_ctx, AVPacket* p)
{
	pthread_mutex_lock (&buffer->mutex);
	int ret = 0;
	// empty buffer
	if (buffer->n_packets == 0)
	// if ((buffer->n_packets == 0) && (buffer->preload == 0))
	{
		ret = EMPTY_BUFFER;
		goto end;
	}

	// if ( buffer->preload < SORTED_PACKETS - 1 ) buffer->preload++;
	// for (int i = 0; i < SORTED_PACKETS; i++)
	// {
	// 	if (sorted_packets_table[i].filled == 0)
	// 	{
	// 		sorted_packets_table[i].filled = 1;
	// 		sorted_packets_table[i].timestamp = int64_timestamp(fmt_ctx, buffer->_front);
	// 		// sorted_packets_table[i].packet = av_packet_alloc();
	// 		av_copy_packet(sorted_packets_table[i].packet, buffer->_front);
	// 		// *sorted_packets_table[i].packet = *buffer->_front;
	// 		// av_copy_packet_side_data(sorted_packets_table[i].packet, buffer->_front);
	// 		// printf("size b %i:  %u\n", i, buffer->_front->size );
	// 		// printf("size p %i:  %u\n", i, sorted_packets_table[i].packet->size );
	// 		// sorted_packets_table[i].packet = *buffer->_front;
	// 		break;
	// 	}
	// }
	// if ( buffer->preload == SORTED_PACKETS - 1)
	// {
	// 		// printf("size: %u\n",sorted_packets_table[0].packet->size );
	// 		// printf("0%llu\n",sorted_packets_table[0].timestamp );
	// 	qsort (sorted_packets_table, SORTED_PACKETS, sizeof(sorted_packets), compare);
	// 		// printf("filled: %u\n",sorted_packets_table[0].filled );

	// 	// *p = *sorted_packets_table[0].packet;
	// 	av_copy_packet(p, sorted_packets_table[0].packet);

	// 		// printf("2%llu\n",sorted_packets_table[0].timestamp );
	// 	// av_packet_unref(sorted_packets_table[0].packet);
	// 	// av_packet_free(&sorted_packets_table[0].packet);
	// 		printf("ts: %llu\n",sorted_packets_table[0].timestamp );
	// 	sorted_packets_table[0].filled = 0;
	// 		// printf("4%lli\n", sorted_packets_table[0].timestamp );
	// }
	// else
	// {
	// 	ret = EMPTY_BUFFER;
	// }
	// // sorted_packets_table[0].timestamp = int64_timestamp(fmt_ctx, p);
	// // printf( "%lli\n", int64_timestamp(fmt_ctx, &sorted_packets_table[0].packet));
	// // sorted_packets_table[0].packet = *buffer->_front;
	// // *p = sorted_packets_table[0].packet;

	// printf( "ts:%i  %lli\n", buffer->_front->flags, int64_timestamp(fmt_ctx, buffer->_front));

	*p = *buffer->_front;
	buffer->_front ++;
	buffer->n_packets --;
	buffer->size_packets -= p->size;
	// loop front pointer back to beginning of the buffer
	if (buffer->_front - buffer->packets == buffer->capacity)
		buffer->_front = buffer->packets;
end:
	pthread_mutex_unlock (&buffer->mutex);
	return ret;
}


void flush_buffer (packet_buffer* buffer)
{
	pthread_mutex_lock (&buffer->mutex);
	while (buffer->_front != buffer->_back)
	{
		av_packet_unref (buffer->_front);
		buffer->_front ++;
		if (buffer->_front - buffer->packets == buffer->capacity)
			buffer->_front = buffer->packets;
	}
	// reset
	buffer->size_packets = 0;
	buffer->n_packets    = 0;
	buffer->_front = buffer->_back = buffer->packets;
	pthread_mutex_unlock (&buffer->mutex);
}
