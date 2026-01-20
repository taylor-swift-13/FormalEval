Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_negative_list :
  sum_product_spec [-2%Z; -10%Z; 10%Z; -2%Z; -2%Z] (-6%Z, 800%Z).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.