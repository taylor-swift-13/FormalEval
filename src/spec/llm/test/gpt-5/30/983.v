Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition Rgtb (x y : R) : bool := if Rgt_dec x y then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => Rgtb x 0) l.

Example get_positive_spec_test :
  get_positive_spec [-2.6958053769612267%R; -3.1836537136945844%R; 33.195768044846155%R; -2.25%R] [33.195768044846155%R].
Proof.
  unfold get_positive_spec.
  simpl.
  replace (Rgtb (-2.6958053769612267%R) 0%R) with false.
  replace (Rgtb (-3.1836537136945844%R) 0%R) with false.
  replace (Rgtb (33.195768044846155%R) 0%R) with true.
  replace (Rgtb (-2.25%R) 0%R) with false.
  simpl.
  reflexivity.
  all: unfold Rgtb.
  all: try (destruct (Rgt_dec (-2.6958053769612267%R) 0%R); [exfalso; lra | reflexivity]).
  all: try (destruct (Rgt_dec (-3.1836537136945844%R) 0%R); [exfalso; lra | reflexivity]).
  all: try (destruct (Rgt_dec (33.195768044846155%R) 0%R); [reflexivity | exfalso; lra]).
  all: try (destruct (Rgt_dec (-2.25%R) 0%R); [exfalso; lra | reflexivity]).
Qed.