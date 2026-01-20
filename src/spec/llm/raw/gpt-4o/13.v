
Require Import Coq.ZArith.ZArith.

Definition gcd_spec (a : Z) (b : Z) (gcd : Z) : Prop :=
  (forall d : Z, d > 0 -> d | a -> d | b -> d | gcd) /\
  gcd > 0 /\
  gcd | a /\
  gcd | b.
