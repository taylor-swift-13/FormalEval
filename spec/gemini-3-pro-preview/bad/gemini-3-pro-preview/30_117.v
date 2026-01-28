Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Fixpoint get_positive_aux (l : list R) : list R :=
  match l with
  | [] => []
  | x :: xs => if Rgt_dec x 0 then x :: get_positive_aux xs else get_positive_aux xs
  end.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = get_positive_aux l.

Example test_get_positive : get_positive_spec [0.5; -4; 2.5; 5; -2.2; -8; -7; -10.5; 9.9; -10.5] [0.5; 2.5; 5; 9.9].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat match goal with
         | [ |- context[Rgt_dec ?x 0] ] => destruct (Rgt_dec x 0); try lra
         end.
  reflexivity.
Qed.