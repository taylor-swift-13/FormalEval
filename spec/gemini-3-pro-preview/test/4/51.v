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

Example test_mad : mean_absolute_deviation_spec [0; 0; 0; 5; 0; 5.7682420395965925] ((10 + 2 * 5.7682420395965925) / 9).
Proof.
  unfold mean_absolute_deviation_spec.
  simpl length.
  replace (INR 6) with 6 by (simpl; lra).
  simpl sum_R.
  replace (0 + (0 + (0 + (5 + (0 + (5.7682420395965925 + 0)))))) with (5 + 5.7682420395965925) by lra.
  simpl map.
  simpl sum_R.
  replace (Rabs (0 - (5 + 5.7682420395965925) / 6)) with ((5 + 5.7682420395965925) / 6) by (unfold Rabs; destruct (Rcase_abs (0 - (5 + 5.7682420395965925) / 6)); lra).
  replace (Rabs (5 - (5 + 5.7682420395965925) / 6)) with (5 - (5 + 5.7682420395965925) / 6) by (unfold Rabs; destruct (Rcase_abs (5 - (5 + 5.7682420395965925) / 6)); lra).
  replace (Rabs (5.7682420395965925 - (5 + 5.7682420395965925) / 6)) with (5.7682420395965925 - (5 + 5.7682420395965925) / 6) by (unfold Rabs; destruct (Rcase_abs (5.7682420395965925 - (5 + 5.7682420395965925) / 6)); lra).
  lra.
Qed.