Require Import List.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_diff (l1 l2: list Z) (acc: Z): Z :=
  match l1, l2 with
  | [], _ => acc
  | _, [] => acc
  | h1 :: t1, h2 :: t2 =>
    if Z.eqb h1 h2 then
      count_diff t1 t2 acc
    else
      count_diff t1 t2 (Z.succ acc)
  end.

Definition smallest_change_impl (arr: list Z): Z :=
  let len := length arr in
  let half_len := (len / 2)%nat in
  let first_half := firstn half_len arr in
  let second_half := skipn (len - half_len) arr in
  count_diff first_half (rev second_half) 0.

Definition problem_73_pre (arr : list Z) : Prop := True.

Definition problem_73_spec (arr: list Z) (n: Z): Prop :=
  n = smallest_change_impl arr.

Example problem_73_test_case_2:
  problem_73_spec [1; 2; 3; 2; 2; 2; 2; 2; 2; 1; 2; 2] 2.
Proof.
  unfold problem_73_spec.
  simpl.
  unfold smallest_change_impl.
  simpl.
  remember (length [1; 2; 3; 2; 2; 2; 2; 2; 2; 1; 2; 2]) as len eqn:Hlen.
  remember (len / 2)%nat as half_len eqn:Hhalf_len.
  remember (firstn half_len [1; 2; 3; 2; 2; 2; 2; 2; 2; 1; 2; 2]) as first_half eqn:Hfirst_half.
  remember (skipn (len - half_len) [1; 2; 3; 2; 2; 2; 2; 2; 2; 1; 2; 2]) as second_half eqn:Hsecond_half.
  simpl in Hfirst_half, Hsecond_half.
  assert (first_half = [1; 2; 3; 2; 2; 2]) by (subst; reflexivity).
  assert (second_half = [2; 2; 2; 1; 2; 2]) by (subst; reflexivity).
  subst first_half second_half.
  simpl.
  reflexivity.
Qed.