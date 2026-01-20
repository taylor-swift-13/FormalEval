Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0 x then true else false) l.

Lemma rltb_nonpos_false (a : R) :
  a <= 0 -> (if Rlt_dec 0 a then true else false) = false.
Proof.
  intros Ha.
  destruct (Rlt_dec 0 a) as [H|H].
  - exfalso; lra.
  - reflexivity.
Qed.

Example get_positive_spec_test :
  get_positive_spec [0; -1.25; -1.5; -0.75; -2.25; -1; -3; -4; -5; -6] [].
Proof.
  unfold get_positive_spec.
  simpl.
  rewrite (rltb_nonpos_false 0) by lra.
  simpl.
  rewrite (rltb_nonpos_false (-1.25)) by lra.
  simpl.
  rewrite (rltb_nonpos_false (-1.5)) by lra.
  simpl.
  rewrite (rltb_nonpos_false (-0.75)) by lra.
  simpl.
  rewrite (rltb_nonpos_false (-2.25)) by lra.
  simpl.
  rewrite (rltb_nonpos_false (-1)) by lra.
  simpl.
  rewrite (rltb_nonpos_false (-3)) by lra.
  simpl.
  rewrite (rltb_nonpos_false (-4)) by lra.
  simpl.
  rewrite (rltb_nonpos_false (-5)) by lra.
  simpl.
  rewrite (rltb_nonpos_false (-6)) by lra.
  simpl.
  reflexivity.
Qed.