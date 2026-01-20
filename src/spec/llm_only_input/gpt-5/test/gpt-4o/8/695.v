Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_mixed_negatives :
  sum_product_spec (4 :: -6 :: -1 :: 8 :: -10 :: nil) (-5, -1920).
Proof.
  unfold sum_product_spec.
  compute.
  reflexivity.
Qed.