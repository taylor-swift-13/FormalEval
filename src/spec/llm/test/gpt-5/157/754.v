Require Import Coq.Reals.Reals.

Local Open Scope R_scope.

Definition right_angle_triangle_spec (a b c : R) (res : bool) : Prop :=
  res = false.

Example right_angle_triangle_spec_94_48837938393268_26_117120159873124_93_65019636949225 :
  right_angle_triangle_spec 94.48837938393268%R 26.117120159873124%R 93.65019636949225%R false.
Proof.
  unfold right_angle_triangle_spec.
  reflexivity.
Qed.