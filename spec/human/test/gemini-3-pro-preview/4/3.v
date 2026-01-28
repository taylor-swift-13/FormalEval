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

Example problem_4_test : problem_4_spec [1; 2; 3; 4; 5] 1.2.
Proof.
  unfold problem_4_spec.
  replace (fold_right Rplus 0 [1; 2; 3; 4; 5] / INR (length [1; 2; 3; 4; 5])) with 3.
  - simpl.
    replace (1 - 3) with (-2) by lra.
    replace (2 - 3) with (-1) by lra.
    replace (3 - 3) with 0 by lra.
    replace (4 - 3) with 1 by lra.
    replace (5 - 3) with 2 by lra.
    rewrite Rabs_R0.
    replace (Rabs (-2)) with 2 by (rewrite Rabs_left; lra).
    replace (Rabs (-1)) with 1 by (rewrite Rabs_left; lra).
    replace (Rabs 1) with 1 by (rewrite Rabs_right; lra).
    replace (Rabs 2) with 2 by (rewrite Rabs_right; lra).
    lra.
  - simpl.
    field.
Qed.