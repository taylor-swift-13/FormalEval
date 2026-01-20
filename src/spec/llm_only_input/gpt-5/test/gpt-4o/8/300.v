Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_with_negative_and_zeros :
  sum_product_spec (-1%Z :: 20%Z :: 30%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: 0%Z :: nil) (49%Z, 0%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.