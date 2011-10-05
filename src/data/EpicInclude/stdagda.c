#include "stdagda.h"
#include <stdlib.h>
#include <unistd.h>
#include <gmp.h>
#include <string.h>
#include <sys/time.h>
#include <locale.h>
//#include "closure.h"


#define _UNICODE
#define UNICODE

void wputStr(char* s) { wprintf(L"%s",s); }

int eqString(char *x, char *y) {
    return strcmp(x, y) == 0;
}

VAL bigZeroRep;
VAL bigOneRep;

VAL bigZero() { return bigZeroRep;}
VAL bigOne() {return bigOneRep;}

void init(void) {
  setlocale(LC_CTYPE, "");

  bigZeroRep = NEWBIGINTVALI(0);
  bigOneRep  = NEWBIGINTVALI(1);
}

void printCharRep(int c) {

  wprintf(L"%lc", c);
}

int bigToInt(VAL n) {
  return (int) mpz_get_si(*(GETBIGINT(n)));
}

VAL intToBig(int n) {
  return NEWBIGINTVALI(n);
} 

VAL getArgBig(VAL num) {
  return evm_getArg(bigToInt(num));
}

VAL numArgsBig(void) { 
  return NEWBIGINTVALI(epic_numArgs());
}

char* charToStr(int x)
{
    char* buf = EMALLOC(2*sizeof(char));
    buf[0] = (char)x; buf[1] = '\0';
    return buf;
}

int eof() { return EOF; }

int charAtBig(char* str, VAL n)
{
    return (int)str[bigToInt(n)];
}

int charAt(char* str, int n) { return (int)str[n]; }

#define STRING_BUFFER_SIZE 1024

int eofstdin() { return feof(stdin);}

char* readStrChunk() { return freadStrChunk(stdin); }

char* freadStrChunk(FILE* f) {
  char* in = EMALLOC(sizeof(char)*STRING_BUFFER_SIZE);
  fgets(in,STRING_BUFFER_SIZE,f);
  return in;
}

void** newArray(VAL size)
{
  return EMALLOC(sizeof(void*)*bigToInt(size));
}

void* arrayIndex(void** array, VAL i)
{
  return array[bigToInt(i)];
}

void setArrayIndex(void** array, VAL i, void* val)
{
  array[bigToInt(i)] = val;
}
