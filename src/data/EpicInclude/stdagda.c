#include "stdagda.h"
#include <stdlib.h>
#include <unistd.h>
#include <gmp.h>
#include <string.h>
#include <sys/time.h>
#include <locale.h>
//#include "closure.h"
#include "stdfuns.h"

#define _UNICODE
#define UNICODE

int eqString(char *x, char *y) {
    return strcmp(x, y) == 0;
}

void init(void) {
  setlocale(LC_CTYPE, "");
}

void printCharRep(int c) {

  wprintf(L"%lc", c);
}

int bigToInt(mpz_t* n) {
  return (int) mpz_get_si(*n);
}

mpz_t* intToBig(int n) {
  mpz_t* answer = EMALLOC(sizeof(mpz_t));
  mpz_init(*answer);
  mpz_set_si(*answer, (signed long int)n);
  return answer; 
} 

VAL getArgBig(mpz_t* num) {
  return evm_getArg(bigToInt(num));
}

mpz_t* numArgsBig(void) { 
  return intToBig(epic_numArgs());
}