Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition Rgt_dec_bool (x : R) : bool :=
  match Rgt_dec x 0 with
  | left _ => true
  | right _ => false
  end.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter Rgt_dec_bool l.

Example test_get_positive : get_positive_spec 
  [0.5; 0; -1.6451572106484336; -4; 2.5; 5; -2.2; -8; 7.7; 9.9; -10.5; 9.9; -13.662203687087855] 
  [0.5; 2.5; 5; 7.7; 9.9; 9.9].
Proof.
  unfold get_positive_spec.
  unfold Rgt_dec_bool.
  repeat (
    simpl;
    match goal with
    | |- context [Rgt_dec ?x 0] =>
        destruct (Rgt_dec x 0);
        try (exfalso; lra)
    end
  ).
  reflexivity.
Qed.