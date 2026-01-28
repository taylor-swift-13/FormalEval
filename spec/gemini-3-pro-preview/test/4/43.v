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

Example test_mad : mean_absolute_deviation_spec [-1; 4.5; 0; 2.5; 7.5] 2.64.
Proof.
  unfold mean_absolute_deviation_spec.
  (* Simplify length first to avoid INR unfolding issues later *)
  simpl length.
  replace (INR 5) with 5 by (simpl; lra).
  
  (* Calculate the mean: sum / len *)
  (* We simplify sum_R specifically to avoid over-simplification *)
  simpl sum_R.
  replace (-1 + (4.5 + (0 + (2.5 + (7.5 + 0))))) with 13.5 by lra.
  replace (13.5 / 5) with 2.7 by lra.
  
  (* Simplify the map and the resulting sum of differences *)
  simpl map.
  simpl sum_R.
  
  (* Compute differences inside absolute values *)
  replace (-1 - 2.7) with (-3.7) by lra.
  replace (4.5 - 2.7) with 1.8 by lra.
  replace (0 - 2.7) with (-2.7) by lra.
  replace (2.5 - 2.7) with (-0.2) by lra.
  replace (7.5 - 2.7) with 4.8 by lra.
  
  (* Evaluate absolute values *)
  (* We use replace with a proof script to evaluate Rabs for specific constants *)
  replace (Rabs (-3.7)) with 3.7 by (unfold Rabs; destruct (Rcase_abs (-3.7)); lra).
  replace (Rabs 1.8) with 1.8 by (unfold Rabs; destruct (Rcase_abs 1.8); lra).
  replace (Rabs (-2.7)) with 2.7 by (unfold Rabs; destruct (Rcase_abs (-2.7)); lra).
  replace (Rabs (-0.2)) with 0.2 by (unfold Rabs; destruct (Rcase_abs (-0.2)); lra).
  replace (Rabs 4.8) with 4.8 by (unfold Rabs; destruct (Rcase_abs 4.8); lra).
  
  (* Final arithmetic check *)
  lra.
Qed.