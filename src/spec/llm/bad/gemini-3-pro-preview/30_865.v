Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec 
  [0.5%R; 0%Z; -4%Z; 2.5%R; 5%Z; -2.2%R; -8%Z; 7.7%R; 9.9%R; -10.5%R; -2.2%R; 0.5%R] 
  [0.5%R; 2.5%R; 5%Z; 7.7%R; 9.9%R; 0.5%R].
Proof.
  unfold get_positive_spec.
  repeat (
    simpl;
    match goal with
    | |- context [Rgt_dec ?x 0] =>
      destruct (Rgt_dec x 0); try lra
    end
  ).
  reflexivity.
Qed.