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

Example problem_4_test : problem_4_spec [7.5; -5.5; 10.416066198571809; 10.416066198571809] 5.60401654964295225.
Proof.
  unfold problem_4_spec.
  replace (fold_right Rplus 0 [7.5; -5.5; 10.416066198571809; 10.416066198571809] /
     INR (length [7.5; -5.5; 10.416066198571809; 10.416066198571809])) with 5.7080330992859045.
  - simpl.
    replace (10.416066198571809 - 5.7080330992859045) with 4.7080330992859045 by lra.
    replace (-5.5 - 5.7080330992859045) with (-11.2080330992859045) by lra.
    replace (7.5 - 5.7080330992859045) with 1.7919669007140955 by lra.
    replace (Rabs 4.7080330992859045) with 4.7080330992859045 by (rewrite Rabs_right; lra).
    replace (Rabs (-11.2080330992859045)) with 11.2080330992859045 by (rewrite Rabs_left1; lra).
    replace (Rabs 1.7919669007140955) with 1.7919669007140955 by (rewrite Rabs_right; lra).
    lra.
  - simpl.
    lra.
Qed.