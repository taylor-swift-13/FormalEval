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

Example problem_4_test : problem_4_spec [-1; -2; -3; 4; 5; -3] 3.
Proof.
  unfold problem_4_spec.
  replace (fold_right Rplus 0 [-1; -2; -3; 4; 5; -3] / INR (length [-1; -2; -3; 4; 5; -3])) with 0.
  - simpl.
    replace (-3 - 0) with (-3) by lra.
    replace (5 - 0) with 5 by lra.
    replace (4 - 0) with 4 by lra.
    replace (-2 - 0) with (-2) by lra.
    replace (-1 - 0) with (-1) by lra.
    replace (Rabs (-3)) with 3 by (rewrite Rabs_left1; lra).
    replace (Rabs 5) with 5 by (rewrite Rabs_right; lra).
    replace (Rabs 4) with 4 by (rewrite Rabs_right; lra).
    replace (Rabs (-2)) with 2 by (rewrite Rabs_left1; lra).
    replace (Rabs (-1)) with 1 by (rewrite Rabs_left1; lra).
    lra.
  - simpl. field.
Qed.