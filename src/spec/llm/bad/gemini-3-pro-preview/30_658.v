Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition check_pos (x : R) : bool :=
  if Rgt_dec x 0 then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter check_pos l.

Example test_get_positive : get_positive_spec [9.9; -2.6958053769612267; 33.195768044846155; -2.25] [9.9; 33.195768044846155].
Proof.
  unfold get_positive_spec, check_pos.
  simpl.
  repeat match goal with
         | |- context [Rgt_dec ?x 0] =>
             destruct (Rgt_dec x 0); try (exfalso; lra)
         end.
  reflexivity.
Qed.