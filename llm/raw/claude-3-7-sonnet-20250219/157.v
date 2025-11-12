
Require Import ZArith.
Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (res : bool) : Prop :=
  res = ((a * a + b * b =? c * c) 
      || (a * a + c * c =? b * b) 
      || (b * b + c * c =? a * a)).
