Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Local Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (res : bool) : Prop :=
  res =
    orb
      (orb (Z.eqb (a * a + b * b) (c * c))
           (Z.eqb (a * a + c * c) (b * b)))
      (Z.eqb (b * b + c * c) (a * a)).

Example right_angle_triangle_spec_762_763_67 :
  right_angle_triangle_spec 762%Z 763%Z 67%Z false.
Proof.
  unfold right_angle_triangle_spec.
  vm_compute.
  reflexivity.
Qed.