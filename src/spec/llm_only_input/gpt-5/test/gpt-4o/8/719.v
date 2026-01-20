Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_test_case :
  sum_product_spec (5%Z :: 3%Z :: 4%Z :: 6%Z :: 7%Z :: 3%Z :: 1%Z :: 2%Z :: 2%Z :: 10%Z :: nil) (43%Z, 302400%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.