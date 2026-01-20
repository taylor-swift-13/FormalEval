Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition is_pos (x : R) : bool :=
  if Rgt_dec x 0 then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter is_pos l.

Example test_get_positive : get_positive_spec 
  [9.9; 25.221353337136023; 33.195768044846155; -2.25; 25.12472520208241; -2.25] 
  [9.9; 25.221353337136023; 33.195768044846155; 25.12472520208241].
Proof.
  unfold get_positive_spec, is_pos.
  simpl.
  repeat (match goal with
          | |- context [Rgt_dec ?x 0] => 
            destruct (Rgt_dec x 0) as [? | ?]; try lra
          end).
  reflexivity.
Qed.