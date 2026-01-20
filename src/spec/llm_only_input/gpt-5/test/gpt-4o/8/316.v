Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_new_test_case :
  sum_product_spec (10%Z :: (-1)%Z :: (-5)%Z :: 30%Z :: (-10)%Z :: 0%Z :: (-8)%Z :: 11%Z :: 30%Z :: 10%Z :: 30%Z :: (-8)%Z :: (-8)%Z :: nil) (81%Z, 0%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.