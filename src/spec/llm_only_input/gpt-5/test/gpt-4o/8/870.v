Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Import ListNotations.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_zero_two_zero_eight_zero :
  sum_product_spec [0%Z; 2%Z; 0%Z; 8%Z; 0%Z] (10%Z, 0%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.