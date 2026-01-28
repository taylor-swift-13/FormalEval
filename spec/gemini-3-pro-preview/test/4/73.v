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

Example test_mad : mean_absolute_deviation_spec 
  [-1; -1; 1; -0.14848795937485382; -5.5; 4] 
  2.05858534010419103.
Proof.
  unfold mean_absolute_deviation_spec.
  simpl length.
  replace (INR 6) with 6 by (simpl; lra).
  
  remember (sum_R [-1; -1; 1; -0.14848795937485382; -5.5; 4] / 6) as mean.
  assert (Hmean: mean = -0.44141465989580897).
  { subst mean. simpl sum_R. lra. }
  
  simpl map.
  simpl sum_R.

  (* Resolve absolute values based on the mean *)
  (* -1 < mean *)
  replace (Rabs (-1 - mean)) with (- (-1 - mean)).
  2: { rewrite Hmean. unfold Rabs. destruct (Rcase_abs (-1 - -0.44141465989580897)); lra. }
  
  (* -1 < mean *)
  replace (Rabs (-1 - mean)) with (- (-1 - mean)).
  2: { rewrite Hmean. unfold Rabs. destruct (Rcase_abs (-1 - -0.44141465989580897)); lra. }
  
  (* 1 > mean *)
  replace (Rabs (1 - mean)) with (1 - mean).
  2: { rewrite Hmean. unfold Rabs. destruct (Rcase_abs (1 - -0.44141465989580897)); lra. }
  
  (* -0.148... > mean *)
  replace (Rabs (-0.14848795937485382 - mean)) with (-0.14848795937485382 - mean).
  2: { rewrite Hmean. unfold Rabs. destruct (Rcase_abs (-0.14848795937485382 - -0.44141465989580897)); lra. }
  
  (* -5.5 < mean *)
  replace (Rabs (-5.5 - mean)) with (- (-5.5 - mean)).
  2: { rewrite Hmean. unfold Rabs. destruct (Rcase_abs (-5.5 - -0.44141465989580897)); lra. }
  
  (* 4 > mean *)
  replace (Rabs (4 - mean)) with (4 - mean).
  2: { rewrite Hmean. unfold Rabs. destruct (Rcase_abs (4 - -0.44141465989580897)); lra. }

  lra.
Qed.