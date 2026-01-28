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

Example problem_4_test : problem_4_spec [-1; 0; 0; 5; 0; 0] (13/9).
Proof.
  unfold problem_4_spec.
  replace (fold_right Rplus 0 [-1; 0; 0; 5; 0; 0] / INR (length [-1; 0; 0; 5; 0; 0])) with (2/3).
  - simpl.
    replace (-1 - 2 / 3) with (-5/3) by lra.
    replace (0 - 2 / 3) with (-2/3) by lra.
    replace (5 - 2 / 3) with (13/3) by lra.
    replace (Rabs (-5 / 3)) with (5/3) by (rewrite Rabs_left1; lra).
    replace (Rabs (-2 / 3)) with (2/3) by (rewrite Rabs_left1; lra).
    replace (Rabs (13 / 3)) with (13/3) by (rewrite Rabs_right; lra).
    lra.
  - simpl. field.
Qed.