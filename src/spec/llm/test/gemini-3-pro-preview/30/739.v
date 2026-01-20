Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec [9.9; -2.6958053769612267; 25.12472520208241; 0.5; -2.6958053769612267] [9.9; 25.12472520208241; 0.5].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat (match goal with
          | [ |- context[Rgt_dec ?x 0] ] => destruct (Rgt_dec x 0); try lra
          end).
  reflexivity.
Qed.