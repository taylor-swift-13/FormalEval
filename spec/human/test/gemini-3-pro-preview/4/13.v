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

Example problem_4_test : problem_4_spec [10; 10; 10] 0.
Proof.
  unfold problem_4_spec.
  replace (fold_right Rplus 0 [10; 10; 10] / INR (length [10; 10; 10])) with 10.
  - simpl.
    replace (10 - 10) with 0 by lra.
    rewrite Rabs_R0.
    lra.
  - simpl.
    field.
Qed.