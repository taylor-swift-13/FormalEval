Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (res : Z * Z) : Prop :=
  let s := fold_right Z.add 0 numbers in
  let p := fold_right Z.mul 1 numbers in
  res = (s, p).

Example test_case_1: sum_product_spec [1; 2; 4; 4; 11; 2; 4; 3] (31, 8448).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.