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

Example problem_4_test : problem_4_spec [-2; 1; 1; 2; 2; 2; -2] (72/49).
Proof.
  unfold problem_4_spec.
  replace (fold_right Rplus 0 [-2; 1; 1; 2; 2; 2; -2] / INR (length [-2; 1; 1; 2; 2; 2; -2])) with (4/7).
  - simpl.
    replace (-2 - 4 / 7) with (-18 / 7) by lra.
    replace (1 - 4 / 7) with (3 / 7) by lra.
    replace (2 - 4 / 7) with (10 / 7) by lra.
    replace (Rabs (-18 / 7)) with (18 / 7) by (rewrite Rabs_left; lra).
    replace (Rabs (3 / 7)) with (3 / 7) by (rewrite Rabs_right; lra).
    replace (Rabs (10 / 7)) with (10 / 7) by (rewrite Rabs_right; lra).
    lra.
  - simpl. field.
Qed.