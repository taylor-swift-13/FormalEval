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

Example problem_4_test : problem_4_spec [1; 1; 1; 2; 2; 2; 1; 10] 1.875.
Proof.
  unfold problem_4_spec.
  replace (fold_right Rplus 0 [1; 1; 1; 2; 2; 2; 1; 10] / INR (length [1; 1; 1; 2; 2; 2; 1; 10])) with 2.5.
  - simpl.
    replace (1 - 2.5) with (-1.5) by lra.
    replace (2 - 2.5) with (-0.5) by lra.
    replace (10 - 2.5) with 7.5 by lra.
    replace (Rabs (-1.5)) with 1.5 by (rewrite Rabs_left1; lra).
    replace (Rabs (-0.5)) with 0.5 by (rewrite Rabs_left1; lra).
    replace (Rabs 7.5) with 7.5 by (rewrite Rabs_right; lra).
    lra.
  - simpl. lra.
Qed.