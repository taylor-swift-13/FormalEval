Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (res : Z * Z) : Prop :=
  let s := fold_right Z.add 0 numbers in
  let p := fold_right Z.mul 1 numbers in
  res = (s, p).

Example test_case_1: sum_product_spec [0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 1%Z; 1%Z; -74%Z; -1%Z; -3%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z] (-76, 0).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.