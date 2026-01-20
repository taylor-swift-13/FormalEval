Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (res : Z * Z) : Prop :=
  let s := fold_right Z.add 0 numbers in
  let p := fold_right Z.mul 1 numbers in
  res = (s, p).

Example test_case_1: sum_product_spec [2%Z; 4%Z; 8%Z; 16%Z; 16%Z; 4%Z; 16%Z; 16%Z; 5%Z; -1%Z; 4%Z] (90, -335544320).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.