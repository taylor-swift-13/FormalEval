Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_test_case :
  sum_product_spec [2%Z; 10%Z; (-5)%Z; (-6)%Z; 30%Z; 0%Z; (-8)%Z; 30%Z; 10%Z; (-8)%Z; 10%Z] (65%Z, 0%Z).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.