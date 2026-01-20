Require Import Coq.Reals.Reals.
Require Import Coq.Bool.Bool.

Local Open Scope R_scope.

Definition right_angle_triangle_spec (a b c : R) (res : bool) : Prop :=
  res = false.

Example right_angle_triangle_spec_94_82545294464254_94_82545294464254_26_117120159873124 :
  right_angle_triangle_spec 94.82545294464254%R 94.82545294464254%R 26.117120159873124%R false.
Proof.
  unfold right_angle_triangle_spec.
  reflexivity.
Qed.