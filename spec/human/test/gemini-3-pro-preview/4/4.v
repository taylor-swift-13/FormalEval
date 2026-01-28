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

Example problem_4_test : problem_4_spec [-1; 4.5; 0; 2.5; -3] 2.32.
Proof.
  unfold problem_4_spec.
  replace (fold_right Rplus 0 [-1; 4.5; 0; 2.5; -3] / INR (length [-1; 4.5; 0; 2.5; -3])) with 0.6.
  - simpl.
    replace (-3 - 0.6) with (-3.6) by lra.
    replace (2.5 - 0.6) with 1.9 by lra.
    replace (0 - 0.6) with (-0.6) by lra.
    replace (4.5 - 0.6) with 3.9 by lra.
    replace (-1 - 0.6) with (-1.6) by lra.
    replace (Rabs (-3.6)) with 3.6 by (rewrite Rabs_left1; lra).
    replace (Rabs 1.9) with 1.9 by (rewrite Rabs_right; lra).
    replace (Rabs (-0.6)) with 0.6 by (rewrite Rabs_left1; lra).
    replace (Rabs 3.9) with 3.9 by (rewrite Rabs_right; lra).
    replace (Rabs (-1.6)) with 1.6 by (rewrite Rabs_left1; lra).
    lra.
  - simpl.
    lra.
Qed.