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

Example test_mad : mean_absolute_deviation_spec [0.0; 0.0; 5.604766823261059; 5.049334549043888] 2.66352534307623675.
Proof.
  unfold mean_absolute_deviation_spec.
  simpl.
  replace (INR 4) with 4 by (simpl; lra).
  unfold Rabs.
  repeat match goal with
         | |- context [Rcase_abs ?x] => destruct (Rcase_abs x); try lra
         end.
Qed.