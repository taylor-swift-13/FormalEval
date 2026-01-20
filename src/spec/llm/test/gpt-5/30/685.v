Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition gt0b (x : R) : bool :=
  match Rlt_dec 0 x with
  | left _ => true
  | right _ => false
  end.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter gt0b l.

Example get_positive_spec_test :
  get_positive_spec
    [9.9%R; 25.221353337136023%R; 24.93175152910768%R; 33.195768044846155%R; (-2.25)%R; 33.195768044846155%R]
    [9.9%R; 25.221353337136023%R; 24.93175152910768%R; 33.195768044846155%R; 33.195768044846155%R].
Proof.
  unfold get_positive_spec.
  simpl.
  unfold gt0b.
  destruct (Rlt_dec 0 9.9%R); [| exfalso; lra].
  simpl.
  unfold gt0b.
  destruct (Rlt_dec 0 25.221353337136023%R); [| exfalso; lra].
  simpl.
  unfold gt0b.
  destruct (Rlt_dec 0 24.93175152910768%R); [| exfalso; lra].
  simpl.
  unfold gt0b.
  destruct (Rlt_dec 0 33.195768044846155%R); [| exfalso; lra].
  simpl.
  unfold gt0b.
  destruct (Rlt_dec 0 (-2.25)%R); [exfalso; lra |].
  simpl.
  unfold gt0b.
  destruct (Rlt_dec 0 33.195768044846155%R); [| exfalso; lra].
  simpl.
  reflexivity.
Qed.