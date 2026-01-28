Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Inductive get_positive_rel : list R -> list R -> Prop :=
| gp_nil : get_positive_rel [] []
| gp_keep : forall x xs ys, x > 0 -> get_positive_rel xs ys -> get_positive_rel (x :: xs) (x :: ys)
| gp_drop : forall x xs ys, x <= 0 -> get_positive_rel xs ys -> get_positive_rel (x :: xs) ys.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  get_positive_rel l res.

Example test_get_positive : get_positive_spec [0; 10.538283343362641; -1.25; -1.5; -0.75; -2.25; -1; -2; 2; -4; -4; -5; -6] [10.538283343362641; 2].
Proof.
  unfold get_positive_spec.
  repeat constructor; lra.
Qed.