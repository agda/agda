dnl ghc.m4 for checking the Glasgow Haskell Compiler

dnl GHC_TRY_COMPILE_HASKELL has 4 arguments
dnl  $1 : Haskell program
dnl  $2 : GHC options (cannot be omitted
dnl  $3 : if succeed to compile
dnl  $4 : if failed to compile
dnl Usually, compiling takes long time, so you should use this function
dnl with AC_MSG_CHECKING and AC_MSG_RESULT to notice users.
dnl
dnl Note: Haskell has an indentation style. So, you should write Haskell code carefully
dnl though sh scripts does not matter indentation. If you have some strange errors,
dnl see config.log to catch your problems.
AC_DEFUN(GHC_TRY_COMPILE_HASKELL,
[cat >CompileTest.hs <<EOF
module CompileTest where
[$1]
EOF
  ghc_compile_haskell='${GHC} -c $GHCFLAGS $2 CompileTest.hs 1>&AC_FD_CC'
  if AC_TRY_EVAL(ghc_compile_haskell) && test -s CompileTest.o; then
      ifelse([$3], , :, [rm -f CompileTest* Main.hi; $3])
  else
      echo "configure: failed program was:" >&AC_FD_CC
      cat CompileTest.hs >&AC_FD_CC
      ifelse([$4], , , [rm -f CompileTest* Main.hi; $4])
  fi
  rm -f CompileTest* Main.hi
])
