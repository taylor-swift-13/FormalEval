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

Example test_mad : mean_absolute_deviation_spec [-1; 4.5; 2.5; -3; -5.5] 3.2.
Proof.
  unfold mean_absolute_deviation_spec.
  simpl length.
  replace (INR 5) with 5 by (simpl; lra).
  
  simpl sum_R.
  replace (-1 + (4.5 + (2.5 + (-3 + (-5.5 + 0))))) with (-2.5) by lra.
  replace (-2.5 / 5) with (-0.5) by lra.
  
  simpl map.
  simpl sum_R.
  
  replace (-1 - -0.5) with (-0.5) by lra.
  replace (4.5 - -0.5) with 5 by lra.
  replace (2.5 - -0.5) with 3 by lra.
  replace (-3 - -0.5) with (-2.5) by lra.
  replace (-5.5 - -0.5) with (-5) by lra.
  
  replace (Rabs (-0.5)) with 0.5 by (unfold Rabs; destruct (Rcase_abs (-0.5)); lra).
  replace (Rabs 5) with 5 by (unfold Rabs; destruct (Rcase_abs 5); lra).
  replace (Rabs 3) with 3 by (unfold Rabs; destruct (Rcase_abs 3); lra).
  replace (Rabs (-2.5)) with 2.5 by (unfold Rabs; destruct (Rcase_abs (-2.5)); lra).
  replace (Rabs (-5)) with 5 by (unfold Rabs; destruct (Rcase_abs (-5)); lra).
  
  lra.
Qed.