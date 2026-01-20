Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Local Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (res : bool) : Prop :=
  res =
    orb
      (orb (Z.eqb (a * a + b * b) (c * c))
           (Z.eqb (a * a + c * c) (b * b)))
      (Z.eqb (b * b + c * c) (a * a)).

Example right_angle_triangle_spec_77_13_226 :
  right_angle_triangle_spec 77%Z 13%Z 226%Z false.
Proof.
  unfold right_angle_triangle_spec.
  vm_compute.
  reflexivity.
Qed.