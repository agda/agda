#include <Rts.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "agda/cpu_info.h"

/// The main closure from Main.hs.
extern StgClosure ZCMain_main_closure;

/// Set the default RtsFlags.
static void agda_set_default_rts_flags(void) {
  // The threaded RTS by default starts a major GC after a program has been idle
  // for 0.3 s. This feature turned out to be annoying, so the idle GC is now by
  // default turned off (-I0).
  RtsFlags.GcFlags.idleGCDelayTime = 0;

  // Get the CPU info:
  AgdaCpuInfo cpu_info = {0};
  if (agda_cpu_info(&cpu_info)) {
    // Set the number of capabilities to equal the number of physical CPU cores:
    if (cpu_info.cpu_count > 0) {
      const uint32_t n = cpu_info.cpu_count;
      fprintf(stderr, "RtsFlags.ParFlags.nCapabilities = %u\n", n);
      RtsFlags.ParFlags.nCapabilities = n;

      // Set the minimum allocation area size:
      if (cpu_info.cpu_cache_size > 0) {
        const uint32_t a =
            (cpu_info.cpu_cache_size / cpu_info.cpu_count) / BLOCK_SIZE;
        fprintf(stderr, "RtsFlags.GcFlags.minAllocAreaSize = %u\n", a);
        RtsFlags.GcFlags.minAllocAreaSize = a;
      }
    }
  }
}

/// The main function for Agda.
int main(int argc, char *argv[]) {

  // Create RTS configuration:
  RtsConfig rts_config = {0};
  memcpy(&rts_config, &defaultRtsConfig, sizeof(RtsConfig));

  // If someone installs Agda with the setuid bit set, then the presence of +RTS
  // may be a security problem (see GHC bug #3910). However, we sometimes
  // recommend people to use +RTS to control Agda's memory usage, so we want
  // this functionality enabled by default.
  rts_config.rts_opts_enabled = RtsOptsAll;

  // Agda tries to optimise the default RTS configuration.
  rts_config.defaultsHook = agda_set_default_rts_flags;

  // Initialise the GHC RTS and evaluate the Haskell main closure:
  return hs_main(argc, argv, &ZCMain_main_closure, rts_config);
}
