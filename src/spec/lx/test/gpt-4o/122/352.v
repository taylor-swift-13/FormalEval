Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition is_at_most_two_digits (n : Z) : bool :=
  (Z.ltb (-100) n) && (Z.ltb n 100).

Definition sum_spec (arr : list Z) (k : nat) (result : Z) : Prop :=
  let first_k_elements := firstn k arr in
  let filtered_elements := filter is_at_most_two_digits first_k_elements in
  result = fold_left Z.add filtered_elements 0.

Example sum_test :
  sum_spec [-99; -89; -77; -55; -44; -21; -22; -11] 4 (-320).
Proof.
  unfold sum_spec.
  simpl.
  reflexivity.
Qed.