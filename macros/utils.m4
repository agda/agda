dnl General macros.

dnl AGDA_GEN_WITH_PROG( PROGRAM-VARIABLE
dnl		      , PROGRAM-NAME
dnl		      , IF-FOUND
dnl		      , IF-NOT-FOUND
dnl		      )
AC_DEFUN(AGDA_GEN_WITH_PROG,
[AC_ARG_WITH($2,
    [AC_HELP_STRING([--with-$2=$1],[use $1 as the path to $2 [default=autodetect]])],
    [$1=$withval],
    [AC_CHECK_TOOL($1,$2)
     AS_IF([test x"${$1}" != x], [$3], [$4])
    ])
])

dnl AGDA_WITH_PROG(PROG,prog)
dnl Looks for required program prog, creates --with-prog flag and
dnl sets PROG to the path to the program.
AC_DEFUN(AGDA_WITH_PROG,
    [AGDA_GEN_WITH_PROG($1,$2,[],[AC_MSG_ERROR([$2 is required])])]
)

dnl AGDA_WITH_OPTIONAL_PROG(PROG,prog)
dnl Looks for optional program prog, creates --with-prog flag and
dnl sets PROG to the path to the program.
dnl Sets the variable HAVE_PROG to Yes or No.
AC_DEFUN(AGDA_WITH_OPTIONAL_PROG,
    [AGDA_GEN_WITH_PROG($1,$2,[HAVE_$1=Yes],
	[HAVE_$1=No
	 $3
	])
     AC_SUBST(HAVE_$1)
    ]
)

dnl Generic way of computing the version of a program.
dnl Looks for the first sequence of digits and dots in the output
dnl of prog --version.
AC_DEFUN(AGDA_VERSION,
[AGDA_CHECK_VERSION($1,$2,$3,$4,
    [${$1} --version | head -1 | sed -e 's/[^0-9]*\([0-9.]*\).*/\1/g'])
])

dnl Combines AGDA_WITH_PROG and AGDA_VERSION. Checks that the version is high enough.
AC_DEFUN(AGDA_WITH_PROG_VERSION,
    [AGDA_WITH_PROG($1,$2)
     AGDA_VERSION($1,$2,[-ge],$3)
    ]
)

dnl Check that the version of a program is satisfactory.
dnl AGDA_CHECK_VERSION( PROGRAM
dnl		      , PROGRAM-NAME
dnl		      , COMPARISON-OPERATOR
dnl		      , VERSION
dnl		      , HOW-TO-COMPUTE-VERSION
dnl		      )
AC_DEFUN(AGDA_CHECK_VERSION,
[
    AC_CACHE_CHECK([for $2 version],$2_version,
		   [
if test x"${$1}" != x; then
    $2_version=[`$5`]
else
    $2_version=""
fi
		   ])
    FP_COMPARE_VERSIONS([${$2_version}],[$3],[$4],[],
			[AC_MSG_ERROR([$2 version $4 or later required])])
    $1_VERSION=${$2_version}
    AC_SUBST($1_VERSION)
])
