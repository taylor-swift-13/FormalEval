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

Example test_mad : mean_absolute_deviation_spec [-1; -2; 5] (26/9).
Proof.
  unfold mean_absolute_deviation_spec.
  simpl length.
  replace (INR 3) with 3 by (simpl; lra).
  
  simpl sum_R.
  replace (-1 + (-2 + (5 + 0))) with 2 by lra.
  
  simpl map.
  simpl sum_R.
  
  replace (-1 - 2 / 3) with (-5 / 3) by lra.
  replace (-2 - 2 / 3) with (-8 / 3) by lra.
  replace (5 - 2 / 3) with (13 / 3) by lra.
  
  replace (Rabs (-5 / 3)) with (5 / 3) by (unfold Rabs; destruct (Rcase_abs (-5 / 3)); lra).
  replace (Rabs (-8 / 3)) with (8 / 3) by (unfold Rabs; destruct (Rcase_abs (-8 / 3)); lra).
  replace (Rabs (13 / 3)) with (13 / 3) by (unfold Rabs; destruct (Rcase_abs (13 / 3)); lra).
  
  lra.
Qed.