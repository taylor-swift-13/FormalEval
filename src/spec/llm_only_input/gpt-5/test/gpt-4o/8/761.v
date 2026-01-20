Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_list_6_6_4_4 :
  sum_product_spec (6%Z :: 6%Z :: 4%Z :: 4%Z :: nil) (20%Z, 576%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.