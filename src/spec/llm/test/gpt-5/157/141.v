Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Local Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (res : bool) : Prop :=
  res =
    orb
      (orb (Z.eqb (a * a + b * b) (c * c))
           (Z.eqb (a * a + c * c) (b * b)))
      (Z.eqb (b * b + c * c) (a * a)).

Example right_angle_triangle_spec_12_226_36 :
  right_angle_triangle_spec 12%Z 226%Z 36%Z false.
Proof.
  unfold right_angle_triangle_spec.
  vm_compute.
  reflexivity.
Qed.