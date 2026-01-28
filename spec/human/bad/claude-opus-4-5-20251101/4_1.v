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

Example test_mad : problem_4_spec [1; 2; 3] (2/3).
Proof.
  unfold problem_4_spec.
  simpl.
  (* Goal should now be about concrete numbers *)
  (* mu = 6/3 = 2, deviations are |1-2|=1, |2-2|=0, |3-2|=1, sum=2, mad=2/3 *)
  
  (* First establish INR 3 = 3 *)
  replace (INR 3) with 3 by (simpl; lra).
  
  (* Compute the mean: (1 + (2 + (3 + 0))) / 3 = 6/3 = 2 *)
  replace (1 + (2 + (3 + 0))) with 6 by lra.
  replace (6 / 3) with 2 by lra.
  
  (* Now compute the absolute deviations *)
  replace (1 - 2) with (-1) by lra.
  replace (2 - 2) with 0 by lra.
  replace (3 - 2) with 1 by lra.
  
  (* Compute the absolute values *)
  rewrite Rabs_Ropp.
  rewrite Rabs_R1.
  rewrite Rabs_R0.
  rewrite Rabs_R1.
  
  (* Now the sum of deviations is 0 + 1 + 0 + 1 = 2 *)
  lra.
Qed.