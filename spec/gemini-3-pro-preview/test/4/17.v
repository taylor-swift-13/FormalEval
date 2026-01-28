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
  [10; 10; 10; 10; 9.232092283615625; 10; 10] 
  (9.2148925966125 / 49).
Proof.
  unfold mean_absolute_deviation_spec.
  simpl length.
  replace (INR 7) with 7 by (simpl; lra).
  
  (* Calculate sum *)
  simpl sum_R.
  replace (10 + (10 + (10 + (10 + (9.232092283615625 + (10 + (10 + 0))))))) 
    with 69.232092283615625 by lra.
  
  (* Simplify map and sum of differences *)
  simpl map.
  simpl sum_R.
  
  (* Calculate differences from mean (69.232... / 7) *)
  (* 10 - mean = 0.109701102340625 *)
  replace (10 - 69.232092283615625 / 7) 
    with 0.109701102340625 by lra.
  
  (* x - mean = 9.232... - mean = -0.65820661404375 *)
  replace (9.232092283615625 - 69.232092283615625 / 7) 
    with (-0.65820661404375) by lra.
    
  (* Evaluate absolute values *)
  replace (Rabs 0.109701102340625) 
    with 0.109701102340625 
    by (unfold Rabs; destruct (Rcase_abs 0.109701102340625); lra).
    
  replace (Rabs (-0.65820661404375)) 
    with 0.65820661404375 
    by (unfold Rabs; destruct (Rcase_abs (-0.65820661404375)); lra).
    
  (* Final arithmetic check *)
  lra.
Qed.