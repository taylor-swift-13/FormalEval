
Require Import Reals.
Require Import List.
Require Import Coq.Reals.Rbasic_fun.

Open Scope R_scope.

Definition sum_list (l : list R) : R :=
  fold_right Rplus 0 l.

Definition length_R (l : list R) : R :=
  INR (length l).

Definition mean (numbers : list R) : R :=
  sum_list numbers / length_R numbers.

Definition abs_diff_from_mean (numbers : list R) : list R :=
  let m := mean numbers in
  map (fun x => Rabs (x - m)) numbers.

Definition mean_absolute_deviation_spec (numbers : list R) (result : R) : Prop :=
  length numbers > 0%nat /\
  let m := mean numbers in
  let abs_diffs := map (fun x => Rabs (x - m)) numbers in
  result = sum_list abs_diffs / length_R numbers.
