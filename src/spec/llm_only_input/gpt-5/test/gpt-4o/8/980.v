Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_new_test :
  sum_product_spec [0%Z; 2%Z; 4%Z; 7%Z; (-3)%Z; (-5)%Z; (-5)%Z; 2%Z] (2%Z, 0%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.