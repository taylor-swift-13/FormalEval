Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition is_positive (x : R) : bool :=
  if Rgt_dec x 0 then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter is_positive l.

Example test_get_positive : get_positive_spec [-89.04346588476734; -2.25; -2.6958053769612267; 7.7] [7.7].
Proof.
  unfold get_positive_spec, is_positive.
  simpl.
  repeat (match goal with
          | |- context [Rgt_dec ?x 0] =>
            destruct (Rgt_dec x 0); [ try lra | try lra ]
          end; simpl).
  reflexivity.
Qed.