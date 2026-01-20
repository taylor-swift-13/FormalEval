Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example get_positive_spec_test :
  get_positive_spec [-2.25%R; -2.25%R; 33.195768044846155%R; -2.25%R] [33.195768044846155%R].
Proof.
  unfold get_positive_spec.
  simpl.
  assert (Hn : ~ (-2.25%R > 0%R)) by lra.
  destruct (Rgt_dec (-2.25%R) 0%R) as [H|H]; [contradiction|].
  simpl.
  destruct (Rgt_dec (-2.25%R) 0%R) as [H'|H']; [contradiction|].
  simpl.
  assert (Hp : 33.195768044846155%R > 0%R) by lra.
  destruct (Rgt_dec 33.195768044846155%R 0%R) as [H2|H2]; [|contradiction].
  simpl.
  destruct (Rgt_dec (-2.25%R) 0%R) as [H3|H3]; [contradiction|].
  simpl.
  reflexivity.
Qed.