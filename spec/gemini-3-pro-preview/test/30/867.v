Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition is_pos (x : R) : bool :=
  if Rgt_dec x 0 then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter is_pos l.

Example test_get_positive : get_positive_spec 
  [9.9%R; 25.221353337136023%R; 24.93175152910768%R; -0.42322814636615796%R; 33.195768044846155%R; -0.5037419809615695%R; -2.6307909667819085%R; -2.25%R] 
  [9.9%R; 25.221353337136023%R; 24.93175152910768%R; 33.195768044846155%R].
Proof.
  unfold get_positive_spec, is_pos.
  simpl.
  repeat (destruct (Rgt_dec _ 0); try lra).
  reflexivity.
Qed.