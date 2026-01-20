Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_negatives_zeros :
  sum_product_spec (-3 :: -7 :: 1 :: -4 :: 0 :: 0 :: 0 :: 0 :: nil) (-13, 0).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.