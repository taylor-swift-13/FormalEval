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

Example test_mad : mean_absolute_deviation_spec [-2; -1; 0; 1; 2] 1.2.
Proof.
  unfold mean_absolute_deviation_spec.
  (* Simplify length first to avoid INR unfolding issues later *)
  simpl length.
  replace (INR 5) with 5 by (simpl; lra).
  
  (* Calculate the mean: sum / len *)
  simpl sum_R.
  replace (-2 + (-1 + (0 + (1 + (2 + 0))))) with 0 by lra.
  replace (0 / 5) with 0 by lra.
  
  (* Simplify the map and the resulting sum of differences *)
  simpl map.
  simpl sum_R.
  
  (* Compute differences inside absolute values *)
  replace (-2 - 0) with (-2) by lra.
  replace (-1 - 0) with (-1) by lra.
  replace (0 - 0) with 0 by lra.
  replace (1 - 0) with 1 by lra.
  replace (2 - 0) with 2 by lra.
  
  (* Evaluate absolute values *)
  replace (Rabs (-2)) with 2 by (unfold Rabs; destruct (Rcase_abs (-2)); lra).
  replace (Rabs (-1)) with 1 by (unfold Rabs; destruct (Rcase_abs (-1)); lra).
  replace (Rabs 0) with 0 by (unfold Rabs; destruct (Rcase_abs 0); lra).
  replace (Rabs 1) with 1 by (unfold Rabs; destruct (Rcase_abs 1); lra).
  replace (Rabs 2) with 2 by (unfold Rabs; destruct (Rcase_abs 2); lra).
  
  (* Final arithmetic check: 1.2 = (2+1+0+1+2)/5 *)
  lra.
Qed.