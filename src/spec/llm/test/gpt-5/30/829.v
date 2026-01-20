Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0 x then true else false) l.

Example get_positive_spec_test :
  get_positive_spec [9.9%R; -2.4785868920126473%R; 9.9%R] [9.9%R; 9.9%R].
Proof.
  unfold get_positive_spec.
  simpl.
  assert (Hpos: 0 < 9.9%R) by lra.
  assert (Hneg: ~(0 < -2.4785868920126473%R)) by lra.
  destruct (Rlt_dec 0 9.9%R) as [H1|H1].
  - simpl.
    destruct (Rlt_dec 0 (-2.4785868920126473%R)) as [H2|H2].
    + exfalso. apply Hneg. exact H2.
    + simpl.
      destruct (Rlt_dec 0 9.9%R) as [H3|H3].
      * reflexivity.
      * exfalso. apply H3. exact Hpos.
  - exfalso. apply H1. exact Hpos.
Qed.