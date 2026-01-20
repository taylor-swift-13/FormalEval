Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_case :
  sum_product_spec (31%Z :: (-10)%Z :: 1%Z :: 10%Z :: 5%Z :: 9%Z :: 8%Z :: (-5)%Z :: 10%Z :: nil) (59%Z, 55800000%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.