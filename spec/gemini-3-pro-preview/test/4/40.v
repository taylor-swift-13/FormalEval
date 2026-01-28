Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Lra.
Import ListNotations.
Open Scope R_scope.

Fixpoint sum_R (l : list R) : R :=
  match l with
  | [] => 0
  | h :: t => h + sum_R t
  end.

Definition mean_absolute_deviation_spec (numbers : list R) (result : R) : Prop :=
  let len := INR (length numbers) in
  let mean := sum_R numbers / len in
  let diffs := map (fun x => Rabs (x - mean)) numbers in
  result = sum_R diffs / len.

Example test_mad : mean_absolute_deviation_spec [-1; -1; 1; 1; -0.14848795937485382] 0.8237580734999766112.
Proof.
  unfold mean_absolute_deviation_spec.
  simpl length.
  replace (INR 5) with 5 by (simpl; lra).
  
  set (x := -0.14848795937485382).
  
  simpl sum_R.
  replace (-1 + (-1 + (1 + (1 + (x + 0))))) with x by (subst x; lra).
  
  simpl map.
  simpl sum_R.
  
  replace (-1 - x / 5) with (-(1 + x/5)) by (subst x; lra).
  replace (-1 - x / 5) with (-(1 + x/5)) by (subst x; lra).
  replace (1 - x / 5) with (1 - x/5) by (subst x; lra).
  replace (1 - x / 5) with (1 - x/5) by (subst x; lra).
  replace (x - x / 5) with (4 * x / 5) by (subst x; lra).
  
  replace (Rabs (-(1 + x/5))) with (1 + x/5) by (unfold Rabs; destruct (Rcase_abs (-(1 + x/5))); subst x; lra).
  replace (Rabs (1 - x/5)) with (1 - x/5) by (unfold Rabs; destruct (Rcase_abs (1 - x/5)); subst x; lra).
  replace (Rabs (4 * x / 5)) with (- (4 * x / 5)) by (unfold Rabs; destruct (Rcase_abs (4 * x / 5)); subst x; lra).
  
  subst x.
  lra.
Qed.