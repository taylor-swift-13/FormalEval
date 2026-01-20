Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_case :
  sum_product_spec [2%Z; 4%Z; 8%Z; 16%Z; 4%Z; 16%Z; 16%Z; 5%Z; (-1)%Z; 4%Z; 20%Z; 20%Z; 11%Z] (125%Z, (-92274688000)%Z).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.