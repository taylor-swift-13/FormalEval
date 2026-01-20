Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_given_list :
  sum_product_spec [4%Z; (-6)%Z; (-7)%Z; (-1)%Z; 1%Z; 30%Z; (-10)%Z] (11%Z, 50400%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.