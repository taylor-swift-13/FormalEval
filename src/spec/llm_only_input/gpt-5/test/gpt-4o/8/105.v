Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_list_1_2_8_16_32 :
  sum_product_spec [1%Z; 2%Z; 8%Z; 16%Z; 32%Z] (59%Z, 8192%Z).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.