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

Example problem_4_test : problem_4_spec [10; 10; 10; 10; 9.232092283615625; 10; 10] (9.2148925966125 / 49).
Proof.
  unfold problem_4_spec.
  replace (fold_right Rplus 0 [10; 10; 10; 10; 9.232092283615625; 10; 10] /
           INR (length [10; 10; 10; 10; 9.232092283615625; 10; 10]))
    with (69.232092283615625 / 7) by (simpl; lra).
  simpl.
  replace (10 - 69.232092283615625 / 7) with (0.767907716384375 / 7) by lra.
  replace (9.232092283615625 - 69.232092283615625 / 7) with (-4.60744629830625 / 7) by lra.
  repeat rewrite Rabs_right by lra.
  repeat rewrite Rabs_left1 by lra.
  lra.
Qed.