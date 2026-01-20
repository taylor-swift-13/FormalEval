Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition Rgt_0_bool (x : R) : bool :=
  if Rgt_dec x 0 then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter Rgt_0_bool l.

Example test_get_positive : get_positive_spec 
  [9.9; 25.12472520208241; 25.12472520208241; 29.75618118087544; 33.195768044846155; -2.25; 33.195768044846155; 25.12472520208241; -2.25] 
  [9.9; 25.12472520208241; 25.12472520208241; 29.75618118087544; 33.195768044846155; 33.195768044846155; 25.12472520208241].
Proof.
  unfold get_positive_spec, filter, Rgt_0_bool.
  repeat (
    match goal with
    | [ |- context [Rgt_dec ?x 0] ] =>
      destruct (Rgt_dec x 0); [ try lra | try lra ]; simpl
    end
  ).
  reflexivity.
Qed.