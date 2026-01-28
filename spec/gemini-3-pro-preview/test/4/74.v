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

Example test_mad : mean_absolute_deviation_spec [1.5; 0.0868013662924878; 0.0868013662924878; 0.0868013662924878] 0.529949487640317075.
Proof.
  unfold mean_absolute_deviation_spec.
  simpl length.
  replace (INR 4) with 4 by (simpl; lra).
  
  simpl sum_R.
  replace (1.5 + (0.0868013662924878 + (0.0868013662924878 + (0.0868013662924878 + 0)))) 
    with 1.7604040988774634 by lra.
  replace (1.7604040988774634 / 4) with 0.44010102471936585 by lra.
  
  simpl map.
  simpl sum_R.
  
  replace (1.5 - 0.44010102471936585) with 1.05989897528063415 by lra.
  replace (0.0868013662924878 - 0.44010102471936585) with (-0.35329965842687805) by lra.
  
  replace (Rabs 1.05989897528063415) with 1.05989897528063415 
    by (unfold Rabs; destruct (Rcase_abs 1.05989897528063415); lra).
  replace (Rabs (-0.35329965842687805)) with 0.35329965842687805 
    by (unfold Rabs; destruct (Rcase_abs (-0.35329965842687805)); lra).
    
  lra.
Qed.