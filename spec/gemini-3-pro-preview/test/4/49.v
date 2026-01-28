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

Example test_mad : mean_absolute_deviation_spec [-1; -2; 5; 9.232092283615625; 4.556069003616063] 3.72610580595707008.
Proof.
  unfold mean_absolute_deviation_spec.
  simpl length.
  replace (INR 5) with 5 by (simpl; lra).
  
  simpl sum_R.
  replace (-1 + (-2 + (5 + (9.232092283615625 + (4.556069003616063 + 0))))) 
    with 15.788161287231688 by lra.
  replace (15.788161287231688 / 5) with 3.1576322574463376 by lra.
  
  simpl map.
  simpl sum_R.
  
  replace (-1 - 3.1576322574463376) with (-4.1576322574463376) by lra.
  replace (-2 - 3.1576322574463376) with (-5.1576322574463376) by lra.
  replace (5 - 3.1576322574463376) with 1.8423677425536624 by lra.
  replace (9.232092283615625 - 3.1576322574463376) with 6.0744600261692874 by lra.
  replace (4.556069003616063 - 3.1576322574463376) with 1.3984367461697254 by lra.
  
  replace (Rabs (-4.1576322574463376)) with 4.1576322574463376 
    by (unfold Rabs; destruct (Rcase_abs (-4.1576322574463376)); lra).
  replace (Rabs (-5.1576322574463376)) with 5.1576322574463376 
    by (unfold Rabs; destruct (Rcase_abs (-5.1576322574463376)); lra).
  replace (Rabs 1.8423677425536624) with 1.8423677425536624 
    by (unfold Rabs; destruct (Rcase_abs 1.8423677425536624); lra).
  replace (Rabs 6.0744600261692874) with 6.0744600261692874 
    by (unfold Rabs; destruct (Rcase_abs 6.0744600261692874); lra).
  replace (Rabs 1.3984367461697254) with 1.3984367461697254 
    by (unfold Rabs; destruct (Rcase_abs 1.3984367461697254); lra).
  
  lra.
Qed.