Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => match Rlt_dec 0 x with | left _ => true | right _ => false end) l.

Example get_positive_spec_test :
  get_positive_spec [9.9%R; 33.195768044846155%R; -2.25%R] [9.9%R; 33.195768044846155%R].
Proof.
  unfold get_positive_spec.
  simpl.
  assert (H1 : 0 < 9.9%R) by lra.
  destruct (Rlt_dec 0 9.9%R) as [H1'|H1']; [| exfalso; lra].
  simpl.
  assert (H2 : 0 < 33.195768044846155%R) by lra.
  destruct (Rlt_dec 0 33.195768044846155%R) as [H2'|H2']; [| exfalso; lra].
  simpl.
  assert (H3 : ~(0 < -2.25%R)) by lra.
  destruct (Rlt_dec 0 (-2.25%R)) as [H3'|H3']; [exfalso; lra |].
  simpl.
  reflexivity.
Qed.