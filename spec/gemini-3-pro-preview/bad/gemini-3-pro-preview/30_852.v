Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition Rgt_bool (x y : R) : bool :=
  if Rgt_dec x y then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => Rgt_bool x 0) l.

Example test_get_positive : get_positive_spec [9.9; 25.221353337136023; 33.195768044846155; -2.25; -2.25; -2.25; 25.221353337136023] [9.9; 25.221353337136023; 33.195768044846155; 25.221353337136023].
Proof.
  unfold get_positive_spec.
  unfold Rgt_bool.
  repeat (simpl; match goal with
                 | |- context [Rgt_dec ?x 0] => destruct (Rgt_dec x 0); try lra
                 end).
  reflexivity.
Qed.