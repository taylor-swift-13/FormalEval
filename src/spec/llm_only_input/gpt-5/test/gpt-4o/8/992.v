Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_case :
  sum_product_spec (1%Z :: Z.opp 74%Z :: Z.opp 10%Z :: nil) (Z.opp 83%Z, 740%Z).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.