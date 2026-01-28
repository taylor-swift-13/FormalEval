Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example test_sum_product_new : sum_product_spec [2; 4; 8; 16; 4; 16; 16; 5; -1; 4; 20; 20; 11] (125, -92274688000).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.