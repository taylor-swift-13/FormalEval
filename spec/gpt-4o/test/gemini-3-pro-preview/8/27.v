Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example test_sum_product_large : sum_product_spec [10; 20; 30; 40; 49] (149, 11760000).
Proof.
  unfold sum_product_spec.
  reflexivity.
Qed.