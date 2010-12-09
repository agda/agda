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
void init(void);
int eqString(char *x, char *y);
void printCharRep(int c);

char* getArgv(mpz_t* n);
mpz_t* getArgc(void);

#endif