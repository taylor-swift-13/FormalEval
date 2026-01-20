Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_list_2_3_5_7_11_14 :
  sum_product_spec (2%Z :: 3%Z :: 5%Z :: 7%Z :: 11%Z :: 14%Z :: nil) (42%Z, 32340%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.