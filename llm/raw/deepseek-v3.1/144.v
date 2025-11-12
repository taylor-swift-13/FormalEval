
Require Import ZArith.

Definition simplify_spec (x : string) (n : string) (result : bool) : Prop :=
  exists x1 x2 n1 n2 : Z,
  x = (String (Ascii.ascii_of_nat x1) "" ++ "/" ++ String (Ascii.ascii_of_nat x2) "") /\
  n = (String (Ascii.ascii_of_nat n1) "" ++ "/" ++ String (Ascii.ascii_of_nat n2) "") /\
  x2 ≠ 0 /\ n2 ≠ 0 /\
  result = (Z.eqb ((x1 * n1) mod (x2 * n2)) 0).
