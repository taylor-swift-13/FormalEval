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

Example test_mad : mean_absolute_deviation_spec [-1; 4.5; 0; 2.5; -3] 2.32.
Proof.
  unfold mean_absolute_deviation_spec.
  (* Simplify length first to avoid INR unfolding issues later *)
  simpl length.
  replace (INR 5) with 5 by (simpl; lra).
  
  (* Calculate the mean: sum / len *)
  simpl sum_R.
  replace (-1 + (4.5 + (0 + (2.5 + (-3 + 0))))) with 3 by lra.
  replace (3 / 5) with 0.6 by lra.
  
  (* Simplify the map and the resulting sum of differences *)
  simpl map.
  simpl sum_R.
  
  (* Compute differences inside absolute values *)
  replace (-1 - 0.6) with (-1.6) by lra.
  replace (4.5 - 0.6) with 3.9 by lra.
  replace (0 - 0.6) with (-0.6) by lra.
  replace (2.5 - 0.6) with 1.9 by lra.
  replace (-3 - 0.6) with (-3.6) by lra.
  
  (* Evaluate absolute values *)
  replace (Rabs (-1.6)) with 1.6 by (unfold Rabs; destruct (Rcase_abs (-1.6)); lra).
  replace (Rabs 3.9) with 3.9 by (unfold Rabs; destruct (Rcase_abs 3.9); lra).
  replace (Rabs (-0.6)) with 0.6 by (unfold Rabs; destruct (Rcase_abs (-0.6)); lra).
  replace (Rabs 1.9) with 1.9 by (unfold Rabs; destruct (Rcase_abs 1.9); lra).
  replace (Rabs (-3.6)) with 3.6 by (unfold Rabs; destruct (Rcase_abs (-3.6)); lra).
  
  (* Final arithmetic check: 2.32 = (1.6 + 3.9 + 0.6 + 1.9 + 3.6) / 5 *)
  lra.
Qed.