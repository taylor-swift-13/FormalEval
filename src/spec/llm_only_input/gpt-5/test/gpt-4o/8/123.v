Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_test :
  sum_product_spec (10%Z :: (-5)%Z :: 30%Z :: 0%Z :: (-8)%Z :: 30%Z :: 10%Z :: nil) (67%Z, 0%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.