Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_case :
  sum_product_spec (3%Z :: 7%Z :: 1%Z :: 4%Z :: 7%Z :: 3%Z :: 2%Z :: 7%Z :: 7%Z :: nil) (41%Z, 172872%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.