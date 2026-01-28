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

Example problem_4_test : problem_4_spec [1; 2; 3] (2/3).
Proof.
  unfold problem_4_spec.
  (* Simplify the mean calculation term first to avoid complex terms inside Rabs *)
  replace (fold_right Rplus 0 [1; 2; 3] / INR (length [1; 2; 3])) with 2.
  - simpl.
    (* Now simplify the specific differences inside Rabs *)
    replace (3 - 2) with 1 by lra.
    replace (2 - 2) with 0 by lra.
    replace (1 - 2) with (-1) by lra.
    
    (* Resolve absolute values *)
    rewrite Rabs_R0.
    replace (Rabs 1) with 1 by (rewrite Rabs_right; lra).
    replace (Rabs (-1)) with 1 by (rewrite Rabs_left1; lra).
    
    (* Final arithmetic verification *)
    lra.
  - (* Proof that the mean is 2 *)
    simpl.
    field.
Qed.