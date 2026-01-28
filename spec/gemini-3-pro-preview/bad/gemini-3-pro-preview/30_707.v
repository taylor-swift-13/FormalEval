Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec [24.93175152910768%R; 33.195768044846155%R; -2.25%R] [24.93175152910768%R; 33.195768044846155%R].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rgt_dec 24.93175152910768%R 0%R); [|lra].
  destruct (Rgt_dec 33.195768044846155%R 0%R); [|lra].
  destruct (Rgt_dec (-2.25)%R 0%R); [lra|].
  reflexivity.
Qed.