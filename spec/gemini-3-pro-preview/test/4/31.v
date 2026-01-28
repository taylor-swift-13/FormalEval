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
  [10; 10; 10; 10; 9.232092283615625; 10; 10; 10; 0] 
  (17.60713161858125 / 9).
Proof.
  unfold mean_absolute_deviation_spec.
  simpl length.
  replace (INR 9) with 9 by (simpl; lra).
  
  (* Calculate sum and mean *)
  replace (sum_R [10; 10; 10; 10; 9.232092283615625; 10; 10; 10; 0]) 
    with 79.232092283615625 by (simpl; lra).
  replace (79.232092283615625 / 9) with 8.803565809290625 by lra.
  
  simpl map.
  simpl sum_R.
  
  (* Calculate differences *)
  replace (10 - 8.803565809290625) with 1.196434190709375 by lra.
  replace (9.232092283615625 - 8.803565809290625) with 0.428526474325 by lra.
  replace (0 - 8.803565809290625) with (-8.803565809290625) by lra.
  
  (* Resolve absolute values *)
  replace (Rabs 1.196434190709375) with 1.196434190709375 
    by (unfold Rabs; destruct (Rcase_abs 1.196434190709375); lra).
  replace (Rabs 0.428526474325) with 0.428526474325 
    by (unfold Rabs; destruct (Rcase_abs 0.428526474325); lra).
  replace (Rabs (-8.803565809290625)) with 8.803565809290625 
    by (unfold Rabs; destruct (Rcase_abs (-8.803565809290625)); lra).
    
  (* Final arithmetic check *)
  lra.
Qed.