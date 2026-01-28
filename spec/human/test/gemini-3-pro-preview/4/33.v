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

Example problem_4_test : problem_4_spec [-2; 2; 2] (16/9).
Proof.
  unfold problem_4_spec.
  replace (fold_right Rplus 0 [-2; 2; 2] / INR (length [-2; 2; 2])) with (2/3).
  - simpl.
    replace (2 - 2 / 3) with (4 / 3) by lra.
    replace (-2 - 2 / 3) with (-8 / 3) by lra.
    replace (Rabs (4 / 3)) with (4 / 3) by (rewrite Rabs_right; lra).
    replace (Rabs (-8 / 3)) with (8 / 3) by (rewrite Rabs_left1; lra).
    lra.
  - simpl.
    field.
Qed.