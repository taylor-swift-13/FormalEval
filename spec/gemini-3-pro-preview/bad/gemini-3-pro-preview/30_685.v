Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Inductive get_positive_R : list R -> list R -> Prop :=
| gp_nil : get_positive_R [] []
| gp_pos : forall x l res, x > 0 -> get_positive_R l res -> get_positive_R (x :: l) (x :: res)
| gp_skip : forall x l res, ~ (x > 0) -> get_positive_R l res -> get_positive_R (x :: l) res.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  get_positive_R l res.

Example test_get_positive : get_positive_spec 
  [9.9; 25.221353337136023; 24.93175152910768; 33.195768044846155; -2.25; 33.195768044846155] 
  [9.9; 25.221353337136023; 24.93175152910768; 33.195768044846155; 33.195768044846155].
Proof.
  unfold get_positive_spec.
  apply gp_pos; [lra |].
  apply gp_pos; [lra |].
  apply gp_pos; [lra |].
  apply gp_pos; [lra |].
  apply gp_skip; [lra |].
  apply gp_pos; [lra |].
  apply gp_nil.
Qed.