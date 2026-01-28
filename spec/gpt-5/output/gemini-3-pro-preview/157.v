Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Local Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (res : bool) : Prop :=
  res =
    orb
      (orb (Z.eqb (a * a + b * b) (c * c))
           (Z.eqb (a * a + c * c) (b * b)))
      (Z.eqb (b * b + c * c) (a * a)).

Example test_right_angle_triangle_3_4_5 : right_angle_triangle_spec 3 4 5 true.
Proof.
  unfold right_angle_triangle_spec.
  simpl.
  reflexivity.
Qed.