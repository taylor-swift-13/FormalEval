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

Example test_mad : mean_absolute_deviation_spec [10; 10; 10; 9.232092283615625] 0.287965393644140625.
Proof.
  unfold mean_absolute_deviation_spec.
  (* Simplify length *)
  simpl length.
  replace (INR 4) with 4 by (simpl; lra).
  
  (* Calculate the mean *)
  simpl sum_R.
  replace (10 + (10 + (10 + (9.232092283615625 + 0)))) with 39.232092283615625 by lra.
  replace (39.232092283615625 / 4) with 9.80802307090390625 by lra.
  
  (* Simplify the map and the resulting sum of differences *)
  simpl map.
  simpl sum_R.
  
  (* Compute differences *)
  replace (10 - 9.80802307090390625) with 0.19197692909609375 by lra.
  replace (9.232092283615625 - 9.80802307090390625) with (-0.57593078728828125) by lra.
  
  (* Evaluate absolute values *)
  replace (Rabs 0.19197692909609375) with 0.19197692909609375 by (unfold Rabs; destruct (Rcase_abs 0.19197692909609375); lra).
  replace (Rabs (-0.57593078728828125)) with 0.57593078728828125 by (unfold Rabs; destruct (Rcase_abs (-0.57593078728828125)); lra).
  
  (* Final arithmetic check *)
  lra.
Qed.