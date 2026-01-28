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

Example problem_4_test : problem_4_spec [0; 0; 0; 5; 0] 1.6.
Proof.
  unfold problem_4_spec.
  replace (fold_right Rplus 0 [0; 0; 0; 5; 0] / INR (length [0; 0; 0; 5; 0])) with 1.
  - simpl.
    replace (0 - 1) with (-1) by lra.
    replace (5 - 1) with 4 by lra.
    replace (Rabs (-1)) with 1 by (rewrite Rabs_left1; lra).
    replace (Rabs 4) with 4 by (rewrite Rabs_right; lra).
    lra.
  - simpl.
    field.
Qed.