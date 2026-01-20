
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Definition fruit_distribution_spec (s : string) (n : Z) (mango_fruits : Z) : Prop :=
  let words := String.split " " s in
  let c1 := Z.of_string (nth 0 words "") in
  let c2 := Z.of_string (nth 3 words "") in
  n - c1 - c2 >= 0 /\ mango_fruits = n - c1 - c2.
