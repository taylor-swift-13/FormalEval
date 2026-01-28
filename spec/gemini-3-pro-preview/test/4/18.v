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

Example test_mad : mean_absolute_deviation_spec 
  [10; 10; 10; 10; 9.232092283615625; 10; 10; 10] 
  0.16797981295908203125.
Proof.
  unfold mean_absolute_deviation_spec.
  simpl length.
  replace (INR 8) with 8 by (simpl; lra).
  
  simpl sum_R.
  replace (10 + (10 + (10 + (10 + (9.232092283615625 + (10 + (10 + (10 + 0)))))))) 
    with 79.232092283615625 by lra.
  replace (79.232092283615625 / 8) with 9.904011535451953125 by lra.
  
  simpl map.
  simpl sum_R.
  
  replace (10 - 9.904011535451953125) with 0.095988464548046875 by lra.
  replace (9.232092283615625 - 9.904011535451953125) with (-0.671919251836328125) by lra.
  
  replace (Rabs 0.095988464548046875) with 0.095988464548046875 
    by (unfold Rabs; destruct (Rcase_abs 0.095988464548046875); lra).
  replace (Rabs (-0.671919251836328125)) with 0.671919251836328125 
    by (unfold Rabs; destruct (Rcase_abs (-0.671919251836328125)); lra).

  lra.
Qed.