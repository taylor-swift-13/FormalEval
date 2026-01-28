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

Example problem_4_test : problem_4_spec [-1; -2; -3; 4; 5] (78/25).
Proof.
  unfold problem_4_spec.
  replace (fold_right Rplus 0 [-1; -2; -3; 4; 5] / INR (length [-1; -2; -3; 4; 5])) with (3/5).
  - simpl.
    replace (5 - 3 / 5) with (22/5) by lra.
    replace (4 - 3 / 5) with (17/5) by lra.
    replace (-3 - 3 / 5) with (-18/5) by lra.
    replace (-2 - 3 / 5) with (-13/5) by lra.
    replace (-1 - 3 / 5) with (-8/5) by lra.
    
    replace (Rabs (22/5)) with (22/5) by (rewrite Rabs_right; lra).
    replace (Rabs (17/5)) with (17/5) by (rewrite Rabs_right; lra).
    replace (Rabs (-18/5)) with (18/5) by (rewrite Rabs_left1; lra).
    replace (Rabs (-13/5)) with (13/5) by (rewrite Rabs_left1; lra).
    replace (Rabs (-8/5)) with (8/5) by (rewrite Rabs_left1; lra).
    
    lra.
  - simpl.
    field.
Qed.