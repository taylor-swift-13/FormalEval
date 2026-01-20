Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_new_test :
  sum_product_spec (-2 :: 0 :: 2 :: 5 :: 7 :: 8 :: 8 :: -3 :: -5 :: -5 :: nil) (15, 0).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.