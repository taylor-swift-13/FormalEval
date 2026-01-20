Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Inductive get_positive_spec : list R -> list R -> Prop :=
| gp_nil : get_positive_spec [] []
| gp_pos : forall x l res, x > 0 -> get_positive_spec l res -> get_positive_spec (x :: l) (x :: res)
| gp_neg : forall x l res, x <= 0 -> get_positive_spec l res -> get_positive_spec (x :: l) res.

Example test_get_positive : get_positive_spec [9.9%R; 25.221353337136023%R; 25.376288083829433%R; -3.1836537136945844%R; -1.5%R] [9.9%R; 25.221353337136023%R; 25.376288083829433%R].
Proof.
  repeat constructor; lra.
Qed.