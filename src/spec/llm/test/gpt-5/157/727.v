Require Import Coq.Reals.Reals.
Require Import Coq.Bool.Bool.

Local Open Scope R_scope.

Definition right_angle_triangle_spec (a b c : R) (res : bool) : Prop :=
  res = false.

Example right_angle_triangle_spec_26_117120159873124_94_48837938393268_94_48837938393268 :
  right_angle_triangle_spec 26.117120159873124%R 94.48837938393268%R 94.48837938393268%R false.
Proof.
  unfold right_angle_triangle_spec.
  reflexivity.
Qed.