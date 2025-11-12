
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint gcd (a b : Z) : Z :=
  if b =? 0 then a else gcd b (Z.rem a b).

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  g = gcd a b /\
  (g | a) /\ (g | b) /\
  (forall d : Z, (d | a) -> (d | b) -> d <= Z.abs g).
