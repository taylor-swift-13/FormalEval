Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Inductive get_positive_R : list R -> list R -> Prop :=
| gp_nil : get_positive_R [] []
| gp_pos : forall x xs ys, x > 0 -> get_positive_R xs ys -> get_positive_R (x :: xs) (x :: ys)
| gp_neg : forall x xs ys, x <= 0 -> get_positive_R xs ys -> get_positive_R (x :: xs) ys.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  get_positive_R l res.

Example test_get_positive : get_positive_spec [-89.04346588476734%R; -2.651030586877352%R; 33.195768044846155%R; 32.97170491287429%R; -2.25%R] [33.195768044846155%R; 32.97170491287429%R].
Proof.
  unfold get_positive_spec.
  apply gp_neg. lra.
  apply gp_neg. lra.
  apply gp_pos. lra.
  apply gp_pos. lra.
  apply gp_neg. lra.
  apply gp_nil.
Qed.