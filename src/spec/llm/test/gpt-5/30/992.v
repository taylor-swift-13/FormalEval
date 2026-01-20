Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition Rgtb (x y : R) : bool :=
  match Rlt_dec y x with
  | left _ => true
  | right _ => false
  end.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => Rgtb x 0) l.

Example get_positive_spec_test :
  get_positive_spec [9.9%R; 33.195768044846155%R; 5.803598881698951%R] [9.9%R; 33.195768044846155%R; 5.803598881698951%R].
Proof.
  unfold get_positive_spec.
  simpl.
  unfold Rgtb.
  destruct (Rlt_dec 0 9.9%R) as [H1|H1]; [|exfalso; apply H1; lra].
  simpl.
  unfold Rgtb.
  destruct (Rlt_dec 0 33.195768044846155%R) as [H2|H2]; [|exfalso; apply H2; lra].
  simpl.
  unfold Rgtb.
  destruct (Rlt_dec 0 5.803598881698951%R) as [H3|H3]; [|exfalso; apply H3; lra].
  simpl.
  reflexivity.
Qed.