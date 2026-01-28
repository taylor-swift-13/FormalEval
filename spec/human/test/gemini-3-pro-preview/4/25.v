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

Example problem_4_test : problem_4_spec [-5.5; 8.006967641333711; -5.5; 10.416066198571809] 7.35575845997638.
Proof.
  unfold problem_4_spec.
  simpl.
  repeat match goal with
  | [ |- context[Rabs ?x] ] =>
    (replace (Rabs x) with x by (rewrite Rabs_right; lra)) ||
    (replace (Rabs x) with (-x) by (rewrite Rabs_left; lra))
  end.
  lra.
Qed.