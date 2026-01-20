Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Inductive get_positive_rel : list R -> list R -> Prop :=
| rel_nil : get_positive_rel [] []
| rel_skip : forall x xs ys, x <= 0 -> get_positive_rel xs ys -> get_positive_rel (x :: xs) ys
| rel_keep : forall x xs ys, x > 0 -> get_positive_rel xs ys -> get_positive_rel (x :: xs) (x :: ys).

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  get_positive_rel l res.

Example test_get_positive : get_positive_spec 
  [0.5; -4; 2.5; 5; -8; -4; -7; 9.9; -11.18889279027017; -10.5; 2.5]
  [0.5; 2.5; 5; 9.9; 2.5].
Proof.
  unfold get_positive_spec.
  apply rel_keep; [lra |].
  apply rel_skip; [lra |].
  apply rel_keep; [lra |].
  apply rel_keep; [lra |].
  apply rel_skip; [lra |].
  apply rel_skip; [lra |].
  apply rel_skip; [lra |].
  apply rel_keep; [lra |].
  apply rel_skip; [lra |].
  apply rel_skip; [lra |].
  apply rel_keep; [lra |].
  apply rel_nil.
Qed.