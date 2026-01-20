Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_negatives :
  sum_product_spec [-9%Z; 4%Z; -10%Z; -6%Z; 5%Z; 0%Z; 8%Z; -10%Z] (-18%Z, 0%Z).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.