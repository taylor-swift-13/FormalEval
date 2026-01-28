Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec [9.9; 25.221353337136023; 33.195768044846155; -2.25; -2.25; -2.25; 9.9] [9.9; 25.221353337136023; 33.195768044846155; 9.9].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat match goal with
         | |- context [if Rgt_dec ?x 0 then _ else _] =>
             destruct (Rgt_dec x 0); try lra
         end.
  reflexivity.
Qed.