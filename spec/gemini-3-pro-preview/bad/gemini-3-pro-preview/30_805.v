Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Inductive get_positive_rel : list R -> list R -> Prop :=
| gp_nil : get_positive_rel [] []
| gp_pos : forall x xs ys, x > 0 -> get_positive_rel xs ys -> get_positive_rel (x :: xs) (x :: ys)
| gp_neg : forall x xs ys, x <= 0 -> get_positive_rel xs ys -> get_positive_rel (x :: xs) ys.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  get_positive_rel l res.

Example test_get_positive : get_positive_spec 
  [9.9; 25.221353337136023; 33.195768044846155; -2.25; 33.195768044846155]
  [9.9; 25.221353337136023; 33.195768044846155; 33.195768044846155].
Proof.
  unfold get_positive_spec.
  apply gp_pos. lra.
  apply gp_pos. lra.
  apply gp_pos. lra.
  apply gp_neg. lra.
  apply gp_pos. lra.
  apply gp_nil.
Qed.