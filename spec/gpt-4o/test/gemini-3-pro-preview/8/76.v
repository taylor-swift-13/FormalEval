Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example test_sum_product : sum_product_spec [2; 4; 8; 1; 16; 4; 16; 16; 5; -1; 2; 4; 16; 10; 8] (111, -53687091200).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.