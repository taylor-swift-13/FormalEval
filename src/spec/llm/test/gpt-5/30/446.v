Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Inductive get_positive_spec : list R -> list R -> Prop :=
| gps_nil : get_positive_spec [] []
| gps_cons_pos : forall x l res, 0 < x -> get_positive_spec l res -> get_positive_spec (x :: l) (x :: res)
| gps_cons_nonpos : forall x l res, ~(0 < x) -> get_positive_spec l res -> get_positive_spec (x :: l) res.

Example get_positive_spec_test :
  get_positive_spec
    [0.5%R; (-4)%R; 2.5%R; 5%R; (-2.2)%R; (-8)%R; (-4)%R; (-7)%R; 9.9%R; (-11.18889279027017)%R; (-10.5)%R; 2.5%R; 9.9%R]
    [0.5%R; 2.5%R; 5%R; 9.9%R; 2.5%R; 9.9%R].
Proof.
  apply gps_cons_pos; [lra|].
  apply gps_cons_nonpos; [apply Rle_not_lt; lra|].
  apply gps_cons_pos; [lra|].
  apply gps_cons_pos; [lra|].
  apply gps_cons_nonpos; [apply Rle_not_lt; lra|].
  apply gps_cons_nonpos; [apply Rle_not_lt; lra|].
  apply gps_cons_nonpos; [apply Rle_not_lt; lra|].
  apply gps_cons_nonpos; [apply Rle_not_lt; lra|].
  apply gps_cons_pos; [lra|].
  apply gps_cons_nonpos; [apply Rle_not_lt; lra|].
  apply gps_cons_nonpos; [apply Rle_not_lt; lra|].
  apply gps_cons_pos; [lra|].
  apply gps_cons_pos; [lra|].
  apply gps_nil.
Qed.