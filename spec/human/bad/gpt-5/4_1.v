Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lra.
Require Import Coq.Init.Nat.
Import ListNotations.

Open Scope R_scope.

Definition problem_4_pre (l : list R) : Prop := l <> [].

Definition problem_4_spec (l : list R) (mad : R) : Prop :=
  let n := length l in
  let mu := fold_right Rplus 0 l / INR n in
  mad = fold_right (fun x acc => acc + Rabs (x - mu)) 0 l / INR n.

Example problem_4_test_pre :
  problem_4_pre [1.0%R; 2.0%R; 3.0%R].
Proof.
  unfold problem_4_pre.
  discriminate.
Qed.

Example problem_4_test_spec :
  problem_4_spec [1.0%R; 2.0%R; 3.0%R] (2/3)%R.
Proof.
  unfold problem_4_spec.
  simpl.
  set (mu := ((1 + (2 + (3 + 0))) / 3)).
  assert (Hmu : mu = 2%R) by (unfold mu; lra).
  rewrite Hmu.
  simpl.
  replace (3 - 2) with 1%R by lra.
  replace (2 - 2) with 0%R by lra.
  replace (1 - 2) with (-1)%R by lra.
  rewrite Rabs_R0.
  rewrite Rabs_Ropp.
  assert (Habs1 : Rabs 1 = 1%R) by (apply Rabs_pos_eq; lra).
  rewrite Habs1.
  rewrite Habs1.
  lra.
Qed.