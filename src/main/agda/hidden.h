#ifndef AGDA_HIDDEN_H
#define AGDA_HIDDEN_H

#include <stdlib.h>

// Portable macro for marking definitions as hidden.
#ifndef HIDDEN
#ifdef __has_attribute
#if __has_attribute(visibility)
#define HIDDEN __attribute__((visibility("hidden")))
#endif
#endif
#ifndef HIDDEN
#define HIDDEN ((void)0)
#endif
#endif

#endif /* AGDA_HIDDEN_H */
