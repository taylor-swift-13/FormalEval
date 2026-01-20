Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_mixed_list :
  sum_product_spec (1%Z :: 2%Z :: (-8)%Z :: 8%Z :: 8%Z :: (-6)%Z :: nil) (5%Z, 6144%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.