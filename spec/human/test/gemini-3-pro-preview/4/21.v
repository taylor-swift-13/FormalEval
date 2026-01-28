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

Example problem_4_test : problem_4_spec [-1; 1; 1; 1] (3/4).
Proof.
  unfold problem_4_spec.
  replace (fold_right Rplus 0 [-1; 1; 1; 1] / INR (length [-1; 1; 1; 1])) with (1/2).
  - simpl.
    replace (1 - 1 / 2) with (1 / 2) by lra.
    replace (-1 - 1 / 2) with (-3 / 2) by lra.
    replace (Rabs (1 / 2)) with (1 / 2) by (rewrite Rabs_right; lra).
    replace (Rabs (-3 / 2)) with (3 / 2) by (rewrite Rabs_left1; lra).
    lra.
  - simpl.
    field.
Qed.