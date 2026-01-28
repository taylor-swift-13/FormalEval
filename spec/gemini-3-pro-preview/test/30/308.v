Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec [0; 77/10; -3/2; -3/4; -9/4; -1; -2; -4; -5; -3; -9/4; 0; -3/4] [77/10].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat match goal with
  | |- context [Rgt_dec ?x 0] => destruct (Rgt_dec x 0); try lra
  end.
  reflexivity.
Qed.