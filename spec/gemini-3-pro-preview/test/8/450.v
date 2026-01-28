Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (res : Z * Z) : Prop :=
  let s := fold_right Z.add 0 numbers in
  let p := fold_right Z.mul 1 numbers in
  res = (s, p).

Example test_case_1: sum_product_spec [1; 10; 5; 9; 8; -5; 11; -5; -10] (24, -9900000).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.