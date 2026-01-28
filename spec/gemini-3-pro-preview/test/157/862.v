Require Import Coq.Reals.Reals.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition right_angle_triangle_spec (a b c : R) (res : bool) : Prop :=
  res = true <-> 
  (a * a + b * b = c * c \/ a * a + c * c = b * b \/ b * b + c * c = a * a).

Example test_right_angle_triangle_real : right_angle_triangle_spec 26.117120159873124 113.29820827740289 26.117120159873124 false.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - intros H. discriminate.
  - intros [H | [H | H]]; lra.
Qed.