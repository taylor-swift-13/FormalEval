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

Example problem_4_test : problem_4_spec [-5.5; 7.5; -5.5; 7.5] 6.5.
Proof.
  unfold problem_4_spec.
  replace (fold_right Rplus 0 [-5.5; 7.5; -5.5; 7.5] / INR (length [-5.5; 7.5; -5.5; 7.5])) with 1.
  - simpl.
    replace (7.5 - 1) with 6.5 by lra.
    replace (-5.5 - 1) with (-6.5) by lra.
    replace (Rabs 6.5) with 6.5 by (rewrite Rabs_right; lra).
    replace (Rabs (-6.5)) with 6.5 by (rewrite Rabs_left; lra).
    lra.
  - simpl.
    lra.
Qed.