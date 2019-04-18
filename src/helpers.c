#include <math.h>
#include <string.h>
#include <stdio.h>
#include <time.h>
#include "rpi_mp_utils.h"

unsigned timer = 0;

void flt_to_s16 (uint8_t *flt, uint8_t **s16, int size)
{
	int         i = 0;
             *s16 = (uint8_t *) malloc (size / 2);
	int16_t    *p = (int16_t *) *s16;
	float     *fp = (float   *) flt;

	for (; i < size / 4; i ++)
		p[i] = (int16_t) floor (fp[i] * 0x7FFF);
}

unsigned long time_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    return (ts.tv_sec*1000000 + ts.tv_nsec/1000) / 1000;
}

unsigned long time_us(void) {
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    return (ts.tv_sec*1000000 + ts.tv_nsec/1000);
}

void ts(void)
{
	timer = time_ms();
}

unsigned long te(void)
{
	return time_ms() - timer;
}

void tp(void)
{
	printf("%lu\n",time_ms() - timer);
}

