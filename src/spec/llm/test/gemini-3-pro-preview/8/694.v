Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (res : Z * Z) : Prop :=
  let s := fold_right Z.add 0 numbers in
  let p := fold_right Z.mul 1 numbers in
  res = (s, p).

Example test_case_1: sum_product_spec [3; 7; 1; 0; 4; 7; 3; 7; 2; 2; -8] (28, 0).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.