#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ(2.52)
AC_INIT([Agda], [2.0], [ulfn@cs.chalmers.se])

#
# Check for programs
#

# Building Agda
AGDA_WITH_PROG_VERSION(GHC,ghc,6.2)
AGDA_WITH_PROG_VERSION(ALEX,alex,2.0)
AGDA_WITH_PROG_VERSION(HAPPY,happy,1.14)

# We need to know if we have ghc 6.4
FP_COMPARE_VERSIONS($GHC_VERSION,[-ge],6.4,
    [HAVE_GHC_6_4=Yes],[HAVE_GHC_6_4=No]
)
AC_SUBST(HAVE_GHC_6_4)

# Building the documentation
AGDA_WITH_OPTIONAL_PROG(HADDOCK,haddock,
    [AC_MSG_WARN(haddock is needed to build parts of the documentation.)]
)

AGDA_WITH_OPTIONAL_PROG(LATEX,latex)
AGDA_WITH_OPTIONAL_PROG(PDFLATEX,pdflatex)

AS_IF([test $HAVE_LATEX == No -a $HAVE_PDFLATEX == No],
      [AC_MSG_WARN(You need at least one of latex and pdflatex to build parts of the documentation.)
      ]
)

# Utility programs
AC_PROG_CC
AC_PROG_INSTALL
AGDA_WITH_OPTIONAL_PROG(WGET,wget)
AGDA_WITH_PROG(FALSE,false)
AGDA_WITH_OPTIONAL_PROG(DARCS,darcs)

# Output
AC_CONFIG_FILES([mk/config.mk])
AC_OUTPUT
