#ifndef _STDAGDA_H
#define _STDAGDA_H

# ifndef WIN32
#  include <pthread.h>
#  define GC_THREADS
# else
#  define GC_WIN32_THREADS
# endif

#include <gc/gc.h>
#include <gmp.h>
#include <stdio.h>
#include "stdfuns.h"
void init(void);
int eqString(char *x, char *y);
void printCharRep(int c);

void wputStr(char* s);

int bigToInt(VAL n);
VAL intToBig(int n);

VAL getArgBig(VAL num);

VAL numArgsBig(void);

FILE* getStdin (void);
FILE* getStdout(void);


char* charToStr(int x);
int charAt(char* str, int n);
int charAtBig(char* str, VAL n);

int eof();

char* freadStrChunk(FILE* f);
// void* freadStrChunk(void* h);

#endif