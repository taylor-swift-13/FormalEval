Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_negative_and_zeros :
  sum_product_spec [-5%Z; 30%Z; 0%Z; 30%Z; 30%Z; 30%Z] (115%Z, 0%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.