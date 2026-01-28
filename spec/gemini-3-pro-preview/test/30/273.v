Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition is_positive (x : R) : bool :=
  if Rgt_dec x 0 then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter is_positive l.

Example test_get_positive : get_positive_spec [0.5; 0; 2.5; -3.144306649398891; 5; -2.2; -8; -0.75; 7.7; 9.9; -10.5] [0.5; 2.5; 5; 7.7; 9.9].
Proof.
  unfold get_positive_spec, is_positive.
  repeat (
    simpl;
    match goal with
    | |- context [if Rgt_dec ?x 0 then _ else _] =>
        destruct (Rgt_dec x 0); [ try lra | try lra ]
    end
  ).
  reflexivity.
Qed.