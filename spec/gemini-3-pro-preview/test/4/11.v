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

Example test_mad : mean_absolute_deviation_spec [-5.5; 7.5; -5.5; 7.5] 6.5.
Proof.
  unfold mean_absolute_deviation_spec.
  simpl length.
  replace (INR 4) with 4 by (simpl; lra).
  
  simpl sum_R.
  replace (-5.5 + (7.5 + (-5.5 + (7.5 + 0)))) with 4 by lra.
  replace (4 / 4) with 1 by lra.
  
  simpl map.
  simpl sum_R.
  
  replace (-5.5 - 1) with (-6.5) by lra.
  replace (7.5 - 1) with 6.5 by lra.
  
  replace (Rabs (-6.5)) with 6.5 by (unfold Rabs; destruct (Rcase_abs (-6.5)); lra).
  replace (Rabs 6.5) with 6.5 by (unfold Rabs; destruct (Rcase_abs 6.5); lra).
  
  lra.
Qed.