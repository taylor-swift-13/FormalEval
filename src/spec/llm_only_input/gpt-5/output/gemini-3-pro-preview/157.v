Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> 
  (a ^ 2 + b ^ 2 = c ^ 2 \/ a ^ 2 + c ^ 2 = b ^ 2 \/ b ^ 2 + c ^ 2 = a ^ 2).

Example right_angle_triangle_spec_test :
  right_angle_triangle_spec 3%Z 4%Z 5%Z true.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - intros _. left. compute. reflexivity.
  - intros _. reflexivity.
Qed.