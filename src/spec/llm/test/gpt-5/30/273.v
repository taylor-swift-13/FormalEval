Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition Rgtb (x y : R) : bool :=
  if Rgt_dec x y then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => Rgtb x 0) l.

Lemma Rgtb_true : forall x y, x > y -> Rgtb x y = true.
Proof.
  intros x y H.
  unfold Rgtb.
  destruct (Rgt_dec x y) as [H'|H']; [reflexivity|exfalso; apply H'; exact H].
Qed.

Lemma Rgtb_false : forall x y, ~(x > y) -> Rgtb x y = false.
Proof.
  intros x y H.
  unfold Rgtb.
  destruct (Rgt_dec x y) as [H'|H']; [exfalso; apply H; exact H'|reflexivity].
Qed.

Example get_positive_spec_test :
  get_positive_spec
    [0.5%R; 0%R; 2.5%R; (-3.144306649398891)%R; 5%R; (-2.2)%R; (-8)%R; (-0.75)%R; 7.7%R; 9.9%R; (-10.5)%R]
    [0.5%R; 2.5%R; 5%R; 7.7%R; 9.9%R].
Proof.
  unfold get_positive_spec.
  simpl.
  rewrite (Rgtb_true 0.5 0); [simpl | lra].
  rewrite (Rgtb_false 0 0); [simpl | lra].
  rewrite (Rgtb_true 2.5 0); [simpl | lra].
  rewrite (Rgtb_false (-3.144306649398891) 0); [simpl | lra].
  rewrite (Rgtb_true 5 0); [simpl | lra].
  rewrite (Rgtb_false (-2.2) 0); [simpl | lra].
  rewrite (Rgtb_false (-8) 0); [simpl | lra].
  rewrite (Rgtb_false (-0.75) 0); [simpl | lra].
  rewrite (Rgtb_true 7.7 0); [simpl | lra].
  rewrite (Rgtb_true 9.9 0); [simpl | lra].
  rewrite (Rgtb_false (-10.5) 0); [simpl | lra].
  reflexivity.
Qed.