Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example test_sum_product_1 : sum_product_spec [2%Z; 4%Z; 8%Z; 16%Z; 16%Z; 4%Z; 16%Z; 16%Z; 5%Z; -1%Z; 2%Z; 4%Z; 16%Z; 4%Z; 4%Z; 2%Z] (118, -343597383680).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.