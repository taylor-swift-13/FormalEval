Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Inductive get_positive_rel : list R -> list R -> Prop :=
| gp_nil : get_positive_rel [] []
| gp_skip : forall x xs ys, x <= 0 -> get_positive_rel xs ys -> get_positive_rel (x :: xs) ys
| gp_keep : forall x xs ys, x > 0 -> get_positive_rel xs ys -> get_positive_rel (x :: xs) (x :: ys).

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  get_positive_rel l res.

Example test_get_positive : get_positive_spec [24.93175152910768%R; -2.25%R] [24.93175152910768%R].
Proof.
  unfold get_positive_spec.
  apply gp_keep.
  - lra.
  - apply gp_skip.
    + lra.
    + apply gp_nil.
Qed.