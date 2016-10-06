#include <stdint.h>

union cast {
  double   x;
  uint64_t n;
};

int identical (double x, double y) {
  union cast cx = { .x = x };
  union cast cy = { .x = y };
  return cx.n == cy.n;
}
