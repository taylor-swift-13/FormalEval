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

Example problem_4_test : problem_4_spec [-1; -1; 1; 1; -0.14848795937485382] 0.8237580734999766112.
Proof.
  unfold problem_4_spec.
  simpl.
  repeat match goal with
  | |- context [Rabs ?x] =>
    (rewrite (Rabs_left x) by lra) || (rewrite (Rabs_right x) by lra)
  end.
  lra.
Qed.