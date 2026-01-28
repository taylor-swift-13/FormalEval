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

Example mean_absolute_deviation_example :
  problem_4_spec [1.0; 2.0; 3.0] 0.6666666666666666.
Proof.
  unfold problem_4_spec.
  simpl.
  assert (INR (length [1.0; 2.0; 3.0]) = 3).
  { simpl. reflexivity. }
  rewrite H.
  assert (fold_right Rplus 0 [1.0; 2.0; 3.0] = 6.0).
  { simpl. lra. }
  rewrite H0.
  assert (6.0 / 3.0 = 2.0).
  { lra. }
  rewrite H1.
  simpl.
  assert (fold_right (fun x acc => acc + Rabs (x - 2.0)) 0 [1.0; 2.0; 3.0] = 2.0).
  { simpl. unfold Rminus. unfold Rabs. unfold Rplus. lra. }
  rewrite H2.
  assert (2.0 / 3.0 = 0.6666666666666666).
  { lra. }
  rewrite H3.
  reflexivity.
Qed.