Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_case :
  sum_product_spec (2 :: -6 :: 0 :: 8 :: -10 :: 4 :: nil) (-2, 0).
Proof.
  unfold sum_product_spec.
  compute.
  reflexivity.
Qed.