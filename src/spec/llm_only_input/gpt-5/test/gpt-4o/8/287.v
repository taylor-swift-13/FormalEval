Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_nonempty_list :
  sum_product_spec (9%Z :: 10%Z :: (-5)%Z :: (-10)%Z :: 0%Z :: (-8)%Z :: 30%Z :: 10%Z :: 10%Z :: nil) (46%Z, 0%Z).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.