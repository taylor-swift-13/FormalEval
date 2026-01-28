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
  [-5.5; 8.006967641333711; -5.5; 10.416066198571809] 
  7.35575845997638.
Proof.
  unfold mean_absolute_deviation_spec.
  simpl length.
  replace (INR 4) with 4 by (simpl; lra).
  
  simpl sum_R.
  replace ((-5.5 + (8.006967641333711 + (-5.5 + (10.416066198571809 + 0)))) / 4)
    with 1.85575845997638 by lra.
  
  simpl map.
  simpl sum_R.
  
  replace (-5.5 - 1.85575845997638) with (-7.35575845997638) by lra.
  replace (8.006967641333711 - 1.85575845997638) with 6.151209181357331 by lra.
  replace (10.416066198571809 - 1.85575845997638) with 8.560307738595429 by lra.
  
  replace (Rabs (-7.35575845997638)) with 7.35575845997638 
    by (unfold Rabs; destruct (Rcase_abs (-7.35575845997638)); lra).
  replace (Rabs 6.151209181357331) with 6.151209181357331 
    by (unfold Rabs; destruct (Rcase_abs 6.151209181357331); lra).
  replace (Rabs 8.560307738595429) with 8.560307738595429 
    by (unfold Rabs; destruct (Rcase_abs 8.560307738595429); lra).
  
  lra.
Qed.