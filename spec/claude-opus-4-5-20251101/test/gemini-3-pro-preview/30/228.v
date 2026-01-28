Require Import List.
Require Import ZArith.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Inductive get_positive_rel : list R -> list R -> Prop :=
| gp_nil : get_positive_rel [] []
| gp_keep : forall x xs ys, x > 0 -> get_positive_rel xs ys -> get_positive_rel (x :: xs) (x :: ys)
| gp_drop : forall x xs ys, ~ (x > 0) -> get_positive_rel xs ys -> get_positive_rel (x :: xs) ys.

Definition get_positive_spec (l : list R) (result : list R) : Prop :=
  get_positive_rel l result.

Example test_get_positive : get_positive_spec [0.5; -4; 2.5; 5; -8; -4; -7; 9.9; -11.18889279027017; -10.5; 2.5] [0.5; 2.5; 5; 9.9; 2.5].
Proof.
  unfold get_positive_spec.
  apply gp_keep; [lra |].
  apply gp_drop; [lra |].
  apply gp_keep; [lra |].
  apply gp_keep; [lra |].
  apply gp_drop; [lra |].
  apply gp_drop; [lra |].
  apply gp_drop; [lra |].
  apply gp_keep; [lra |].
  apply gp_drop; [lra |].
  apply gp_drop; [lra |].
  apply gp_keep; [lra |].
  apply gp_nil.
Qed.