Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_new_test :
  sum_product_spec [6%Z; (-1)%Z; 4%Z; 7%Z; 3%Z; 7%Z; 2%Z] (28%Z, (-7056)%Z).
Proof.
  unfold sum_product_spec.
  simpl.
  vm_compute.
  reflexivity.
Qed.