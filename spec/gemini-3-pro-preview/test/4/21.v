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

Example test_mad : mean_absolute_deviation_spec [-1; 1; 1; 1] 0.75.
Proof.
  unfold mean_absolute_deviation_spec.
  (* Simplify length first to avoid INR unfolding issues later *)
  simpl length.
  replace (INR 4) with 4 by (simpl; lra).
  
  (* Calculate the mean: sum / len *)
  (* We simplify sum_R specifically to avoid over-simplification *)
  simpl sum_R.
  replace (-1 + (1 + (1 + (1 + 0)))) with 2 by lra.
  replace (2 / 4) with 0.5 by lra.
  
  (* Simplify the map and the resulting sum of differences *)
  simpl map.
  simpl sum_R.
  
  (* Compute differences inside absolute values *)
  replace (-1 - 0.5) with (-1.5) by lra.
  replace (1 - 0.5) with 0.5 by lra.
  
  (* Evaluate absolute values *)
  (* We use replace with a proof script to evaluate Rabs for specific constants *)
  replace (Rabs (-1.5)) with 1.5 by (unfold Rabs; destruct (Rcase_abs (-1.5)); lra).
  replace (Rabs 0.5) with 0.5 by (unfold Rabs; destruct (Rcase_abs 0.5); lra).
  
  (* Final arithmetic check *)
  lra.
Qed.