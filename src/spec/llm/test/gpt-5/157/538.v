Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Local Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (res : bool) : Prop :=
  res =
    orb
      (orb (Z.eqb (a * a + b * b) (c * c))
           (Z.eqb (a * a + c * c) (b * b)))
      (Z.eqb (b * b + c * c) (a * a)).

Example right_angle_triangle_spec_2022_65_383 :
  right_angle_triangle_spec 2022%Z 65%Z 383%Z false.
Proof.
  unfold right_angle_triangle_spec.
  vm_compute.
  reflexivity.
Qed.