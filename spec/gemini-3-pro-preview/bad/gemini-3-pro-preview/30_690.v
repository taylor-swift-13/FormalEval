Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Fixpoint filter_pos (l : list R) : list R :=
  match l with
  | [] => []
  | x :: xs => if Rgt_dec x 0 then x :: filter_pos xs else filter_pos xs
  end.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter_pos l.

Example test_get_positive : get_positive_spec 
  [9.9%R; 25.12472520208241%R; 33.195768044846155%R; -2.25%R; 33.195768044846155%R; 25.12472520208241%R; -2.25%R] 
  [9.9%R; 25.12472520208241%R; 33.195768044846155%R; 33.195768044846155%R; 25.12472520208241%R].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat match goal with
  | |- context [Rgt_dec ?x 0] =>
      destruct (Rgt_dec x 0); try (exfalso; lra)
  end.
  reflexivity.
Qed.