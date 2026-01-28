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

Example problem_4_test : problem_4_spec [-1; -2; -3; 5] 2.625.
Proof.
  unfold problem_4_spec.
  replace (fold_right Rplus 0 [-1; -2; -3; 5] / INR (length [-1; -2; -3; 5])) with (-0.25).
  - simpl.
    replace (-1 - -0.25) with (-0.75) by lra.
    replace (-2 - -0.25) with (-1.75) by lra.
    replace (-3 - -0.25) with (-2.75) by lra.
    replace (5 - -0.25) with 5.25 by lra.
    replace (Rabs (-0.75)) with 0.75 by (rewrite Rabs_left; lra).
    replace (Rabs (-1.75)) with 1.75 by (rewrite Rabs_left; lra).
    replace (Rabs (-2.75)) with 2.75 by (rewrite Rabs_left; lra).
    replace (Rabs 5.25) with 5.25 by (rewrite Rabs_right; lra).
    lra.
  - simpl. lra.
Qed.