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

Example problem_4_test : problem_4_spec [0; 0; 4.5; 0] 1.6875.
Proof.
  unfold problem_4_spec.
  replace (fold_right Rplus 0 [0; 0; 4.5; 0] / INR (length [0; 0; 4.5; 0])) with 1.125.
  - simpl.
    replace (4.5 - 1.125) with 3.375 by lra.
    replace (0 - 1.125) with (-1.125) by lra.
    replace (Rabs (-1.125)) with 1.125 by (rewrite Rabs_left1; lra).
    replace (Rabs 3.375) with 3.375 by (rewrite Rabs_right; lra).
    lra.
  - simpl.
    lra.
Qed.