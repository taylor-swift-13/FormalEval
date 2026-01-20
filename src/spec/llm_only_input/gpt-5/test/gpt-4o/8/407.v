Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_test_case :
  sum_product_spec ((Z.opp 3%Z) :: 2%Z :: 3%Z :: 10%Z :: 3%Z :: 20%Z :: 30%Z :: nil) (65%Z, Z.opp 324000%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.