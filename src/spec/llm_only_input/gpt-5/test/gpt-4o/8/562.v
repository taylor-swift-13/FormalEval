Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_13_30_30_neg8 :
  sum_product_spec (13%Z :: 30%Z :: 30%Z :: (-8)%Z :: nil) (65%Z, (-93600)%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.