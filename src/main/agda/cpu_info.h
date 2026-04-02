#ifndef AGDA_CPU_COUNT_H
#define AGDA_CPU_COUNT_H

#include "./hidden.h"
#include <stdbool.h>
#include <stdint.h>

typedef struct {
  // The number of CPU cores.
  uint32_t cpu_count;
  // The size of the largest CPU cache.
  uint32_t cpu_cache_size;
} AgdaCpuInfo;

/// Get the CPU info.
HIDDEN bool agda_cpu_info(AgdaCpuInfo *cpu_info_out);

#endif /* AGDA_CPU_COUNT_H */
