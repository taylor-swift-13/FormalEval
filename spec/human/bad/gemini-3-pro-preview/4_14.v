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

Example problem_4_test : problem_4_spec [10; 10; 10; 10; 9.232092283615625] 0.245730469243.
Proof.
  unfold problem_4_spec.
  set (l := [10; 10; 10; 10; 9.232092283615625]).
  set (mu := fold_right Rplus 0 l / INR (length l)).
  assert (Hmu : mu = 9.846418456723125).
  { subst mu l. simpl. lra. }
  rewrite Hmu.
  subst l.
  simpl.
  repeat rewrite Rabs_right by lra.
  rewrite Rabs_left1 by lra.
  lra.
Qed.