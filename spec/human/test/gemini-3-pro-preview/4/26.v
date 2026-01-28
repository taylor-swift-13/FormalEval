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

Example problem_4_test : problem_4_spec [-1; 4.5; 0; 2.5; -3; -5.5] 2.75.
Proof.
  unfold problem_4_spec.
  (* Simplify the mean calculation term first to avoid complex terms inside Rabs *)
  replace (fold_right Rplus 0 [-1; 4.5; 0; 2.5; -3; -5.5] / INR (length [-1; 4.5; 0; 2.5; -3; -5.5])) with (-5/12).
  - simpl.
    (* Now simplify the specific differences inside Rabs *)
    (* x = -1 *)
    replace (Rabs (-1 - -5/12)) with (- (-1 - -5/12)) by (rewrite Rabs_left; lra).
    (* x = 4.5 *)
    replace (Rabs (4.5 - -5/12)) with (4.5 - -5/12) by (rewrite Rabs_right; lra).
    (* x = 0 *)
    replace (Rabs (0 - -5/12)) with (0 - -5/12) by (rewrite Rabs_right; lra).
    (* x = 2.5 *)
    replace (Rabs (2.5 - -5/12)) with (2.5 - -5/12) by (rewrite Rabs_right; lra).
    (* x = -3 *)
    replace (Rabs (-3 - -5/12)) with (- (-3 - -5/12)) by (rewrite Rabs_left; lra).
    (* x = -5.5 *)
    replace (Rabs (-5.5 - -5/12)) with (- (-5.5 - -5/12)) by (rewrite Rabs_left; lra).
    
    (* Final arithmetic verification *)
    lra.
  - (* Proof that the mean is -5/12 *)
    simpl.
    lra.
Qed.