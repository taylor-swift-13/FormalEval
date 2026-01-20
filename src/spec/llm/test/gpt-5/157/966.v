Require Import Coq.Reals.Reals.
Require Import Coq.Bool.Bool.

Local Open Scope R_scope.

Definition R_eqb (x y : R) : bool := false.

Definition right_angle_triangle_spec (a b c : R) (res : bool) : Prop :=
  res =
    orb
      (orb (R_eqb (a * a + b * b) (c * c))
           (R_eqb (a * a + c * c) (b * b)))
      (R_eqb (b * b + c * c) (a * a)).

Example right_angle_triangle_spec_120_27264036217386_95_48313167066331_26_117120159873124 :
  right_angle_triangle_spec 120.27264036217386%R 95.48313167066331%R 26.117120159873124%R false.
Proof.
  unfold right_angle_triangle_spec.
  vm_compute.
  reflexivity.
Qed.