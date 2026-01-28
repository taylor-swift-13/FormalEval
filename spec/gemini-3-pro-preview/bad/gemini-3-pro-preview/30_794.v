Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition Rgt_bool (x y : R) : bool :=
  if Rgt_dec x y then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => Rgt_bool x 0) l.

Example test_get_positive : get_positive_spec [9.9%R; 25.12472520208241%R; -2.6958053769612267%R; 33.195768044846155%R; -1.9199320509072952%R] [9.9%R; 25.12472520208241%R; 33.195768044846155%R].
Proof.
  unfold get_positive_spec, Rgt_bool.
  simpl.
  destruct (Rgt_dec 9.9 0); [|exfalso; lra].
  destruct (Rgt_dec 25.12472520208241 0); [|exfalso; lra].
  destruct (Rgt_dec (-2.6958053769612267) 0); [exfalso; lra|].
  destruct (Rgt_dec 33.195768044846155 0); [|exfalso; lra].
  destruct (Rgt_dec (-1.9199320509072952) 0); [exfalso; lra|].
  reflexivity.
Qed.