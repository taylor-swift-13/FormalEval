Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition pos_dec (x : R) : bool :=
  if Rgt_dec x 0 then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter pos_dec l.

Example test_get_positive : get_positive_spec [33.195768044846155; -2.25] [33.195768044846155].
Proof.
  unfold get_positive_spec, pos_dec.
  destruct (Rgt_dec 33.195768044846155 0); [| lra].
  destruct (Rgt_dec (-2.25) 0); [lra |].
  simpl.
  reflexivity.
Qed.