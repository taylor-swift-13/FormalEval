Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition Rgtb (x y : R) : bool :=
  if Rgt_dec x y then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => Rgtb x 0) l.

Example test_get_positive : get_positive_spec 
  [0.5; -4; 2.5; 5; -11.18889279027017; -8; -4; -7; 9.9; -11.18889279027017; -10.5] 
  [0.5; 2.5; 5; 9.9].
Proof.
  unfold get_positive_spec.
  unfold Rgtb.
  repeat (
    simpl;
    match goal with
    | |- context [Rgt_dec ?x ?y] =>
      destruct (Rgt_dec x y);
      [ try (exfalso; lra) | try (exfalso; lra) ]
    end
  ).
  reflexivity.
Qed.