Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec [9.9%R; 25.221353337136023%R; 24.93175152910768%R; 33.195768044846155%R; -3.1836537136945844%R; -1.5%R] [9.9%R; 25.221353337136023%R; 24.93175152910768%R; 33.195768044846155%R].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat match goal with
  | |- context [if Rgt_dec ?x 0 then _ else _] =>
      destruct (Rgt_dec x 0); [ try lra | try lra ]
  end.
  simpl.
  reflexivity.
Qed.