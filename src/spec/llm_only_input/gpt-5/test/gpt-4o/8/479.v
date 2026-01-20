Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_mixed_list :
  sum_product_spec (2 :: 10 :: -4 :: 3 :: -5 :: 3 :: 0 :: -8 :: -4 :: 10 :: nil) (7, 0).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.