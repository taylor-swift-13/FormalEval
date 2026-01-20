Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_with_negatives_and_zero :
  sum_product_spec (4%Z :: 3%Z :: 0%Z :: (Z.opp 8%Z) :: (Z.opp 8%Z) :: (Z.opp 8%Z) :: nil) (Z.opp 17%Z, 0%Z).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.