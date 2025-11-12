
Definition right_angle_triangle_spec (a : nat) (b : nat) (c : nat) (result : bool) : Prop :=
  result = true ↔ (a * a + b * b = c * c ∨ a * a + c * c = b * b ∨ b * b + c * c = a * a).
