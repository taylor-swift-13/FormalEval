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

Example problem_4_test : problem_4_spec [0; 0; 5] (20/9).
Proof.
  unfold problem_4_spec.
  replace (fold_right Rplus 0 [0; 0; 5] / INR (length [0; 0; 5])) with (5/3).
  - simpl.
    replace (5 - 5 / 3) with (10 / 3) by lra.
    replace (0 - 5 / 3) with (-5 / 3) by lra.
    replace (Rabs (10 / 3)) with (10 / 3) by (rewrite Rabs_right; lra).
    replace (Rabs (-5 / 3)) with (5 / 3) by (rewrite Rabs_left1; lra).
    lra.
  - simpl.
    field.
Qed.