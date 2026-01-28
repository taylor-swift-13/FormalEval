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

Example test_mad : mean_absolute_deviation_spec [0; 0; 0; 5.049334549043888] 1.893500455891458.
Proof.
  unfold mean_absolute_deviation_spec.
  simpl length.
  replace (INR 4) with 4 by (simpl; lra).
  simpl sum_R.
  replace (0 + (0 + (0 + (5.049334549043888 + 0)))) with 5.049334549043888 by lra.
  replace (5.049334549043888 / 4) with 1.262333637260972 by lra.
  simpl map.
  simpl sum_R.
  replace (0 - 1.262333637260972) with (-1.262333637260972) by lra.
  replace (5.049334549043888 - 1.262333637260972) with 3.787000911782916 by lra.
  replace (Rabs (-1.262333637260972)) with 1.262333637260972 by (unfold Rabs; destruct (Rcase_abs (-1.262333637260972)); lra).
  replace (Rabs 3.787000911782916) with 3.787000911782916 by (unfold Rabs; destruct (Rcase_abs 3.787000911782916); lra).
  lra.
Qed.