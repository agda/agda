/* From the ieee754 package. See the LICENSE file. */

#include <stdint.h>

union double_t {
  double d;
  uint64_t w;
};

int
identical (double x, double y)
{
  union double_t ux = { x };
  union double_t uy = { y };
  return ux.w == uy.w;
}
