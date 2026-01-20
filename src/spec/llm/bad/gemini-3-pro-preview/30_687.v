Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Inductive get_positive_spec : list R -> list R -> Prop :=
| gp_nil : get_positive_spec [] []
| gp_keep : forall x l res, x > 0 -> get_positive_spec l res -> get_positive_spec (x :: l) (x :: res)
| gp_skip : forall x l res, x <= 0 -> get_positive_spec l res -> get_positive_spec (x :: l) res.

Example test_get_positive : get_positive_spec [-89.04346588476734%R; 32.97170491287429%R; -2.6958053769612267%R; 7.7%R] [32.97170491287429%R; 7.7%R].
Proof.
  apply gp_skip.
  - lra.
  - apply gp_keep.
    + lra.
    + apply gp_skip.
      * lra.
      * apply gp_keep.
        -- lra.
        -- apply gp_nil.
Qed.