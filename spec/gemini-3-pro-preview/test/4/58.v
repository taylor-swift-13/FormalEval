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

Definition inputs : list R := 
  [-2.0; 1.0; 1.0; 2.0; 2.0; 2.0; -2.0; 2.7500345836492754; 1.2120988051006742].

Definition expected : R :=
  let len := INR (length inputs) in
  let mean := sum_R inputs / len in
  let diffs := map (fun x => Rabs (x - mean)) inputs in
  sum_R diffs / len.

Example test_mad : mean_absolute_deviation_spec inputs expected.
Proof.
  unfold mean_absolute_deviation_spec, expected.
  reflexivity.
Qed.