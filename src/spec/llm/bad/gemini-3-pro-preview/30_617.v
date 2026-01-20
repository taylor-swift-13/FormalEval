Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Fixpoint filter_pos (l : list R) : list R :=
  match l with
  | [] => []
  | x :: xs => if Rlt_dec 0 x then x :: filter_pos xs else filter_pos xs
  end.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter_pos l.

Example test_get_positive : get_positive_spec [3/2; 27/10; -36/10; 0; 5] [3/2; 27/10; 5].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat (match goal with
          | |- context [Rlt_dec ?a ?b] => destruct (Rlt_dec a b); try lra
          end).
  reflexivity.
Qed.