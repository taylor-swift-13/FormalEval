Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Inductive get_positive_rel : list R -> list R -> Prop :=
| gp_nil : get_positive_rel [] []
| gp_cons_pos : forall x l res, x > 0 -> get_positive_rel l res -> get_positive_rel (x :: l) (x :: res)
| gp_cons_neg : forall x l res, ~ (x > 0) -> get_positive_rel l res -> get_positive_rel (x :: l) res.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  get_positive_rel l res.

Example test_get_positive : get_positive_spec [9.9; -2.25; 9.9] [9.9; 9.9].
Proof.
  unfold get_positive_spec.
  apply gp_cons_pos.
  - lra.
  - apply gp_cons_neg.
    + lra.
    + apply gp_cons_pos.
      * lra.
      * apply gp_nil.
Qed.