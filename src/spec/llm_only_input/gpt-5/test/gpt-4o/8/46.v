Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_negative_values :
  sum_product_spec [-1%Z; -3%Z; 4%Z; -3%Z] (-3, -36).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.