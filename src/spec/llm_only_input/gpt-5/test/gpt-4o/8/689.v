Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_list_2_5_8_minus3 :
  sum_product_spec (2%Z :: 5%Z :: 8%Z :: (-3)%Z :: nil) (12%Z, (-240)%Z).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.