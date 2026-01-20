Require Import List.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint count_diff (l1 l2: list nat) (acc: nat): nat :=
  match l1, l2 with
  | [], _ => acc
  | _, [] => acc
  | h1 :: t1, h2 :: t2 =>
    if Nat.eqb h1 h2 then
      count_diff t1 t2 acc
    else
      count_diff t1 t2 (S acc)
  end.

Definition smallest_change_spec (arr: list nat) (n: nat): Prop :=
  let len := length arr in
  let half_len := len / 2 in
  let first_half := firstn half_len arr in
  let second_half := skipn (len - half_len) arr in
  n = count_diff first_half (rev second_half) 0.

Example smallest_change_test :
  smallest_change_spec [2; 3; 1; 9; 10; 8; 6; 3; 2] 2.
Proof.
  unfold smallest_change_spec.
  simpl.
  reflexivity.
Qed.