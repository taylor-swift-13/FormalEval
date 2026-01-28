Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Inductive get_positive_R : list R -> list R -> Prop :=
| gp_nil : get_positive_R [] []
| gp_cons_pos : forall x l res, 
    x > 0 -> get_positive_R l res -> get_positive_R (x :: l) (x :: res)
| gp_cons_neg : forall x l res, 
    x <= 0 -> get_positive_R l res -> get_positive_R (x :: l) res.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  get_positive_R l res.

Example test_get_positive : get_positive_spec 
  [0.5; 0; 24.93175152910768; -4; 2.5; 5; -2.2; -2.651030586877352; -8; 7.7; 9.9; -10.5; 9.9; -8]
  [0.5; 24.93175152910768; 2.5; 5; 7.7; 9.9; 9.9].
Proof.
  unfold get_positive_spec.
  repeat (apply gp_cons_pos; [lra | ] || apply gp_cons_neg; [lra | ]).
  apply gp_nil.
Qed.