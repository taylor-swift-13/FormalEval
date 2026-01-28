Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example test_sum_product_numbers : sum_product_spec [13; 20; 5; 40; 49] (127, 2548000).
Proof.
  unfold sum_product_spec.
  reflexivity.
Qed.