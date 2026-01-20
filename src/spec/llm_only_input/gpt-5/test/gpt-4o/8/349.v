Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_mixed_signs :
  sum_product_spec (1%Z :: Z.opp 1%Z :: 1%Z :: Z.opp 1%Z :: 1%Z :: 1%Z :: Z.opp 1%Z :: nil) (1%Z, Z.opp 1%Z).
Proof.
  unfold sum_product_spec.
  compute.
  reflexivity.
Qed.