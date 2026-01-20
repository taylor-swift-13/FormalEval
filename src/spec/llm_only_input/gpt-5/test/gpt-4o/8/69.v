Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_case :
  sum_product_spec (2%Z :: 4%Z :: 8%Z :: 16%Z :: 16%Z :: 3%Z :: 40%Z :: nil) (89%Z, 1966080%Z).
Proof.
  vm_compute.
  reflexivity.
Qed.