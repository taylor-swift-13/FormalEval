Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_case :
  sum_product_spec (1%Z :: 4%Z :: 8%Z :: 16%Z :: 32%Z :: 8%Z :: 50%Z :: nil) (119%Z, 6553600%Z).
Proof.
  unfold sum_product_spec.
  reflexivity.
Qed.