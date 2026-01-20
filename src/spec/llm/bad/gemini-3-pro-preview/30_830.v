Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec 
  [9.9; 25.221353337136023; 24.93175152910768; 12.829932365585156; 33.195768044846155; -3.1836537136945844; -1.5] 
  [9.9; 25.221353337136023; 24.93175152910768; 12.829932365585156; 33.195768044846155].
Proof.
  unfold get_positive_spec.
  cbv [filter].
  repeat match goal with
  | |- context [Rgt_dec ?x 0] =>
      destruct (Rgt_dec x 0);
      [ try (exfalso; lra) | try (exfalso; lra) ]
  end.
  reflexivity.
Qed.