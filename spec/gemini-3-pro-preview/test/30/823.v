Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition is_pos (x : R) : bool :=
  if Rgt_dec x 0 then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter is_pos l.

Example test_get_positive : get_positive_spec 
  [-2.651030586877352%R; 37.590357356685196%R; 33.195768044846155%R; -2.25%R] 
  [37.590357356685196%R; 33.195768044846155%R].
Proof.
  unfold get_positive_spec, is_pos.
  repeat (
    simpl;
    match goal with
    | |- context [Rgt_dec ?x 0] =>
        destruct (Rgt_dec x 0);
        [ try lra | try lra ]
    end
  ).
  reflexivity.
Qed.