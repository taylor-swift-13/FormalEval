Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Inductive get_positive_R : list R -> list R -> Prop :=
| gp_nil : get_positive_R [] []
| gp_pos : forall x xs ys, x > 0 -> get_positive_R xs ys -> get_positive_R (x :: xs) (x :: ys)
| gp_neg : forall x xs ys, x <= 0 -> get_positive_R xs ys -> get_positive_R (x :: xs) ys.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  get_positive_R l res.

Example test_get_positive : get_positive_spec [0.5; -4; 2.5; 5; -2.2; -8; -4; -7; -10.5; 9.9; -10.5] [0.5; 2.5; 5; 9.9].
Proof.
  unfold get_positive_spec.
  apply gp_pos; [lra |].
  apply gp_neg; [lra |].
  apply gp_pos; [lra |].
  apply gp_pos; [lra |].
  apply gp_neg; [lra |].
  apply gp_neg; [lra |].
  apply gp_neg; [lra |].
  apply gp_neg; [lra |].
  apply gp_neg; [lra |].
  apply gp_pos; [lra |].
  apply gp_neg; [lra |].
  apply gp_nil.
Qed.