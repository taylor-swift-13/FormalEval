Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition Rgtb (x y : R) : bool :=
  if Rlt_dec y x then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => Rgtb x 0%R) l.

Example get_positive_spec_test :
  get_positive_spec [1.5%R; 2.7%R; -3.6%R; 0%R; 5%R] [1.5%R; 2.7%R; 5%R].
Proof.
  unfold get_positive_spec.
  simpl.
  unfold Rgtb.
  destruct (Rlt_dec 0%R 1.5%R); [| lra].
  simpl.
  unfold Rgtb.
  destruct (Rlt_dec 0%R 2.7%R); [| lra].
  simpl.
  unfold Rgtb.
  destruct (Rlt_dec 0%R (-3.6%R)); [lra |].
  simpl.
  unfold Rgtb.
  destruct (Rlt_dec 0%R 0%R); [lra |].
  simpl.
  unfold Rgtb.
  destruct (Rlt_dec 0%R 5%R); [| lra].
  simpl.
  reflexivity.
Qed.