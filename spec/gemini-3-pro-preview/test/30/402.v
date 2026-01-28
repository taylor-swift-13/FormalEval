Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Inductive get_positive_spec : list R -> list R -> Prop :=
| gp_nil : get_positive_spec [] []
| gp_cons_pos : forall x l res, x > 0 -> get_positive_spec l res -> get_positive_spec (x :: l) (x :: res)
| gp_cons_neg : forall x l res, x <= 0 -> get_positive_spec l res -> get_positive_spec (x :: l) res.

Example test_get_positive : get_positive_spec 
  [-3; 0.5; -4; 2.5; 5; -2.2; 0.3470794389448922; -8; -4; -7; -10.5; 9.9; -10.5] 
  [0.5; 2.5; 5; 0.3470794389448922; 9.9].
Proof.
  apply gp_cons_neg; [lra | ].
  apply gp_cons_pos; [lra | ].
  apply gp_cons_neg; [lra | ].
  apply gp_cons_pos; [lra | ].
  apply gp_cons_pos; [lra | ].
  apply gp_cons_neg; [lra | ].
  apply gp_cons_pos; [lra | ].
  apply gp_cons_neg; [lra | ].
  apply gp_cons_neg; [lra | ].
  apply gp_cons_neg; [lra | ].
  apply gp_cons_neg; [lra | ].
  apply gp_cons_pos; [lra | ].
  apply gp_cons_neg; [lra | ].
  apply gp_nil.
Qed.