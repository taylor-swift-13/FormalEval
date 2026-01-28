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

Example test_mad : mean_absolute_deviation_spec [1; 1; 1; 2; 2; 2; 1; 10; 10; 1] 2.76.
Proof.
  unfold mean_absolute_deviation_spec.
  (* Simplify length first to avoid INR unfolding issues later *)
  simpl length.
  replace (INR 10) with 10 by (simpl; lra).
  
  (* Calculate the mean: sum / len *)
  simpl sum_R.
  replace (1 + (1 + (1 + (2 + (2 + (2 + (1 + (10 + (10 + (1 + 0)))))))))) with 31 by lra.
  replace (31 / 10) with 3.1 by lra.
  
  (* Simplify the map and the resulting sum of differences *)
  simpl map.
  simpl sum_R.
  
  (* Compute differences inside absolute values *)
  replace (1 - 3.1) with (-2.1) by lra.
  replace (2 - 3.1) with (-1.1) by lra.
  replace (10 - 3.1) with 6.9 by lra.
  
  (* Evaluate absolute values *)
  replace (Rabs (-2.1)) with 2.1 by (unfold Rabs; destruct (Rcase_abs (-2.1)); lra).
  replace (Rabs (-1.1)) with 1.1 by (unfold Rabs; destruct (Rcase_abs (-1.1)); lra).
  replace (Rabs 6.9) with 6.9 by (unfold Rabs; destruct (Rcase_abs 6.9); lra).
  
  (* Final arithmetic check *)
  lra.
Qed.