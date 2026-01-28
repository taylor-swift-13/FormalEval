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

Example problem_4_test : problem_4_spec [-1; -2; 5; -1] (19/8).
Proof.
  unfold problem_4_spec.
  (* Simplify the mean calculation term first to avoid complex terms inside Rabs *)
  replace (fold_right Rplus 0 [-1; -2; 5; -1] / INR (length [-1; -2; 5; -1])) with (1/4).
  - simpl.
    (* Now simplify the specific differences inside Rabs *)
    replace (-1 - 1/4) with (-5/4) by lra.
    replace (-2 - 1/4) with (-9/4) by lra.
    replace (5 - 1/4) with (19/4) by lra.
    
    (* Resolve absolute values *)
    replace (Rabs (-5/4)) with (5/4) by (rewrite Rabs_left1; lra).
    replace (Rabs (-9/4)) with (9/4) by (rewrite Rabs_left1; lra).
    replace (Rabs (19/4)) with (19/4) by (rewrite Rabs_right; lra).
    
    (* Final arithmetic verification *)
    lra.
  - (* Proof that the mean is 1/4 *)
    simpl.
    field.
Qed.