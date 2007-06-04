module Where where

-- all these examples should not termination check

f : forall {A : Set} -> A
f {A} = g
      where g : A
            g = f


f1 : forall {A : Set} -> A -> A
f1 {A} a = g a
      where g : A -> A
            g a = f1 a


f2 : forall {A : Set} -> A -> A
f2 {A} a = g a
      where g : A -> A
            g = f2 



