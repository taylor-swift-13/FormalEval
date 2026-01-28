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

Example problem_4_test : problem_4_spec [1; 1; 1; 2; 2; 2; 1; 10; 10; 1] (276/100).
Proof.
  unfold problem_4_spec.
  replace (fold_right Rplus 0 [1; 1; 1; 2; 2; 2; 1; 10; 10; 1] /
           INR (length [1; 1; 1; 2; 2; 2; 1; 10; 10; 1])) with (31/10).
  - simpl.
    replace (1 - 31 / 10) with (-21 / 10) by lra.
    replace (2 - 31 / 10) with (-11 / 10) by lra.
    replace (10 - 31 / 10) with (69 / 10) by lra.
    replace (Rabs (-21 / 10)) with (21 / 10) by (rewrite Rabs_left1; lra).
    replace (Rabs (-11 / 10)) with (11 / 10) by (rewrite Rabs_left1; lra).
    replace (Rabs (69 / 10)) with (69 / 10) by (rewrite Rabs_right; lra).
    lra.
  - simpl. field.
Qed.