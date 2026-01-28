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

Example test_mad : mean_absolute_deviation_spec [7.5; -5.5; 10.416066198571809; 10.416066198571809] 5.60401654964295225.
Proof.
  unfold mean_absolute_deviation_spec.
  simpl length.
  replace (INR 4) with 4 by (simpl; lra).
  
  simpl sum_R.
  replace (7.5 + (-5.5 + (10.416066198571809 + (10.416066198571809 + 0)))) with 22.832132397143618 by lra.
  replace (22.832132397143618 / 4) with 5.7080330992859045 by lra.
  
  simpl map.
  simpl sum_R.
  
  replace (7.5 - 5.7080330992859045) with 1.7919669007140955 by lra.
  replace (-5.5 - 5.7080330992859045) with (-11.2080330992859045) by lra.
  replace (10.416066198571809 - 5.7080330992859045) with 4.7080330992859045 by lra.
  
  replace (Rabs 1.7919669007140955) with 1.7919669007140955 by (unfold Rabs; destruct (Rcase_abs 1.7919669007140955); lra).
  replace (Rabs (-11.2080330992859045)) with 11.2080330992859045 by (unfold Rabs; destruct (Rcase_abs (-11.2080330992859045)); lra).
  replace (Rabs 4.7080330992859045) with 4.7080330992859045 by (unfold Rabs; destruct (Rcase_abs 4.7080330992859045); lra).
  
  lra.
Qed.