#include "./cpu_info.h"
#include "./hidden.h"
#include <stdint.h>

#if defined(_WIN32)
#include <assert.h>
#include <malloc.h>
#include <windows.h>
#elif defined(__APPLE__)
#include <sys/sysctl.h>
#elif defined(__OpenBSD__) || defined(__FreeBSD__) || defined(__NetBSD__) ||   \
    defined(__DragonFly__)
#include <sys/sysctl.h>
#elif __linux
#if __has_include(<unistd.h>)
#include <unistd.h>
#endif
#endif

/******************************************************************************
 * Windows
 *****************************************************************************/
#if defined(_WIN32)

typedef BOOL(WINAPI *LPFN_GLPI)(PSYSTEM_LOGICAL_PROCESSOR_INFORMATION, PDWORD);

HIDDEN bool agda_cpu_info(AgdaCpuInfo *cpu_info_out) {
  if (cpu_info_out == NULL) {
    return false;
  }

  // Load the symbol for GetLogicalProcessorInformation.
  const LPFN_GLPI glpi = (LPFN_GLPI)GetProcAddress(
      GetModuleHandle(TEXT("kernel32")), "GetLogicalProcessorInformation");

  // If GetLogicalProcessorInformation is not available, fall back to
  // GetSystemInfo.
  if (glpi == NULL) {
    SYSTEM_INFO system_info = {0};
    GetSystemInfo(&system_info);

    // Write out the number of CPU cores:
    cpu_info_out->cpu_count = system_info.dwNumberOfProcessors;

    // GetSystemInfo does not provide the CPU cache sizes:
    cpu_info_out->cpu_cache_size = 0;

    return true;
  }
  assert(glpi != NULL);

  // Get the buffer length required to get all logical processor information.
  DWORD return_length = 0;
  {
    const BOOL status = glpi(NULL, &return_length);
    assert(status == FALSE);
    (void)status;
    assert(GetLastError() == ERROR_INSUFFICIENT_BUFFER);
    assert(return_length > 0);
  }
  // Allocate a buffer of the required length.
  PSYSTEM_LOGICAL_PROCESSOR_INFORMATION buffer = malloc(return_length);
  if (buffer == NULL) {
    return 0;
  }
  // Get all logical processor information.
  {
    const BOOL status = glpi(buffer, &return_length);
    assert(status == TRUE);
    (void)status;
  }
  // Count the number of logical processors that correspond to a physical CPU
  // core.
  DWORD byte_offset = 0;
  PSYSTEM_LOGICAL_PROCESSOR_INFORMATION buffer_ptr = buffer;
  uint32_t cpu_count = 0;
  DWORD cpu_l1_cache_size = 0;
  DWORD cpu_l2_cache_size = 0;
  DWORD cpu_l3_cache_size = 0;
  while (byte_offset + sizeof(SYSTEM_LOGICAL_PROCESSOR_INFORMATION) <=
         return_length) {
    switch (buffer_ptr->Relationship) {
    case RelationProcessorCore:
      ++cpu_count;
      break;
    case RelationCache:
      if (buffer_ptr->Cache.Type == CacheData ||
          buffer_ptr->Cache.Type == CacheUnified) {
        if (buffer_ptr->Cache.Level == 1 &&
            buffer_ptr->Cache.Size > cpu_l1_cache_size) {
          cpu_l1_cache_size = buffer_ptr->Cache.Size;
        }
        if (buffer_ptr->Cache.Level == 2 &&
            buffer_ptr->Cache.Size > cpu_l2_cache_size) {
          cpu_l2_cache_size = buffer_ptr->Cache.Size;
        }
        if (buffer_ptr->Cache.Level == 3 &&
            buffer_ptr->Cache.Size > cpu_l3_cache_size) {
          cpu_l3_cache_size = buffer_ptr->Cache.Size;
        }
      }
      break;
    default:
      break;
    }
    byte_offset += sizeof(SYSTEM_LOGICAL_PROCESSOR_INFORMATION);
    ++buffer_ptr;
  }
  // Free the buffer.
  free(buffer);
  // Write out the number of CPU cores:
  cpu_info_out->cpu_count = cpu_count;
  // Write out the size of the largest CPU cache:
  {
    uint32_t cpu_cache_size = 0;
    if (cpu_l1_cache_size > cpu_cache_size) {
      cpu_cache_size = cpu_l1_cache_size;
    }
    if (cpu_l2_cache_size > cpu_cache_size) {
      cpu_cache_size = cpu_l2_cache_size;
    }
    if (cpu_l3_cache_size > cpu_cache_size) {
      cpu_cache_size = cpu_l3_cache_size;
    }
    cpu_info_out->cpu_cache_size = cpu_cache_size;
  }
  return true;
}

/******************************************************************************
 * macOS
 *****************************************************************************/
#elif defined(__APPLE__)

#define TRY_SYSCTL(query, query_out)                                           \
  (sysctlbyname((query), &(query_out), &(size_t){sizeof((query_out))}, NULL,   \
                0) == 0)

HIDDEN bool agda_cpu_info(AgdaCpuInfo *cpu_info_out) {
  if (cpu_info_out == NULL) {
    return false;
  }

  // Determine the number of CPU cores:
  {
    int cpu_count = 0;
    // Try the number of physical Apple Silicon performance cores.
    if (!TRY_SYSCTL("hw.perflevel0.physicalcpu", cpu_count)) {
      // Try the number of physical CPU cores.
      if (!TRY_SYSCTL("hw.physicalcpu", cpu_count)) {
        // Try the number of logical Apple Silicon performance cores.
        if (!TRY_SYSCTL("hw.perflevel0.logicalcpu", cpu_count)) {
          // Try the number of logical CPU cores.
          if (!TRY_SYSCTL("hw.logicalcpu", cpu_count)) {
            // Give up.
          }
        }
      }
    }
    cpu_info_out->cpu_count = cpu_count > 0 ? cpu_count : 0;
  }

  // Determine the size of the largest CPU cache:
  {
    int cpu_cache_size = 0;
    // Try the L3 cache for the Apple Silicon performance cores.
    if (!TRY_SYSCTL("hw.perflevel0.l3cachesize", cpu_cache_size)) {
      // Try the L3 cache.
      if (!TRY_SYSCTL("hw.l3cachesize", cpu_cache_size)) {
        // Try the L2 cache for the Apple Silicon performance cores.
        if (!TRY_SYSCTL("hw.perflevel0.l2cachesize", cpu_cache_size)) {
          // Try the L2 cache.
          if (!TRY_SYSCTL("hw.l2cachesize", cpu_cache_size)) {
            // Try the L1 data cache for the Apple Silicon performance cores.
            if (!TRY_SYSCTL("hw.perflevel0.l1dcachesize", cpu_cache_size)) {
              // Try the L1 data cache.
              if (!TRY_SYSCTL("hw.l1dcachesize", cpu_cache_size)) {
                // Give up.
              }
            }
          }
        }
      }
    }
    cpu_info_out->cpu_cache_size = cpu_cache_size > 0 ? cpu_cache_size : 0;
  }
  return true;
}

/******************************************************************************
 * BSD
 *****************************************************************************/
#elif defined(__OpenBSD__) || defined(__FreeBSD__) || defined(__NetBSD__) ||   \
    defined(__DragonFly__)

#define TRY_SYSCTL(query, query_out)                                           \
  (sysctlbyname((query), &(query_out), &(size_t){sizeof((query_out))}, NULL,   \
                0) == 0)

HIDDEN bool agda_cpu_info(AgdaCpuInfo *cpu_info_out) {
  if (cpu_info_out == NULL) {
    return false;
  }

  // Determine the number of CPU cores:
  {
    int cpu_count = 0;
    // Try the number of CPU cores currently online.
    if (!TRY_SYSCTL("hw.ncpuonline", cpu_count)) {
      // Try the number of CPU cores configured.
      if (!TRY_SYSCTL("hw.ncpu", cpu_count)) {
        // Give up.
      }
    }
    cpu_info_out->cpu_count = cpu_count > 0 ? cpu_count : 0;
  }

  // Determine the size of the largest CPU cache:
  {
    // TODO:
    // There doesn't appear to be an easy way to do this on FreeBSD,
    // and I have not looked into OpenBSD, NetBSD, or DragonflyBSD.
    cpu_info_out->cpu_cache_size = 0;
  }
  return true;
}

/******************************************************************************
 * POSIX
 *****************************************************************************/
#elif __linux

HIDDEN bool agda_cpu_info(AgdaCpuInfo *cpu_info_out) {
  if (cpu_info_out == NULL) {
    return false;
  }

  // Determine the number of CPU cores:
  {
    long cpu_count = 0;
    // Try number of CPU cores currently online.
#if __has_include(<unistd.h>) && defined(_SC_NPROCESSORS_ONLN)
    if (cpu_count <= 0) {
      cpu_count = sysconf(_SC_NPROCESSORS_ONLN);
    }
#endif
    // Try number of CPU cores configured.
#if __has_include(<unistd.h>) && defined(_SC_NPROCESSORS_CONF)
    if (cpu_count <= 0) {
      cpu_count = sysconf(_SC_NPROCESSORS_CONF);
    }
#endif
    cpu_info_out->cpu_count = cpu_count > 0 ? cpu_count : 0;
  }

  // Determine the size of the largest CPU cache:
  {
    // TODO:
    // It appears this requires reading the files that match:
    //
    //   /sys/devices/system/cpu/cpu*/cache/index*/size
    //
    cpu_info_out->cpu_cache_size = 0;
  }
  return true;
}

/******************************************************************************
 * Default
 *****************************************************************************/
#else

HIDDEN bool agda_cpu_info(AgdaCpuInfo *cpu_info_out) { return false; }

#endif /* __APPLE__ */
