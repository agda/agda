dnl Macros to get the version of various programs.

dnl ghc
AC_DEFUN(AGDA_GHC_VERSION,
    [AGDA_CHECK_VERSION($1,ghc,[-lt],$2,[${$1} --numeric-version])]
)

dnl alex
AC_DEFUN(AGDA_ALEX_VERSION,[AGDA_VERSION($1,alex,[-lt],$2)])

dnl happy
AC_DEFUN(AGDA_HAPPY_VERSION,[AGDA_VERSION($1,happy,[-lt],$2)])
