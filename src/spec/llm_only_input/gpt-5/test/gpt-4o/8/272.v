Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_mixed_list :
  sum_product_spec (-10 :: 0 :: 6 :: 10 :: 5 :: 9 :: 8 :: (-5) :: nil) (23, 0).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.