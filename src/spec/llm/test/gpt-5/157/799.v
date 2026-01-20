Require Import Coq.Reals.Reals.
Require Import Coq.Bool.Bool.

Local Open Scope R_scope.

Definition Reqb (x y : R) : bool := false.

Definition right_angle_triangle_spec (a b c : R) (res : bool) : Prop :=
  res =
    orb
      (orb (Reqb (a * a + b * b) (c * c))
           (Reqb (a * a + c * c) (b * b)))
      (Reqb (b * b + c * c) (a * a)).

Example right_angle_triangle_spec_94_48837938393268_26_117120159873124 :
  right_angle_triangle_spec 94.48837938393268%R 26.117120159873124%R 26.117120159873124%R false.
Proof.
  unfold right_angle_triangle_spec.
  reflexivity.
Qed.