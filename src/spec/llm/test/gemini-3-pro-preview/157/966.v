Require Import Coq.Reals.Reals.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition right_angle_triangle_spec (a b c : R) (res : bool) : Prop :=
  res = true <-> 
  (a ^ 2 + b ^ 2 = c ^ 2 \/ a ^ 2 + c ^ 2 = b ^ 2 \/ b ^ 2 + c ^ 2 = a ^ 2).

Example test_right_angle_triangle_float : right_angle_triangle_spec 120.27264036217386 95.48313167066331 26.117120159873124 false.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - intros H. inversion H.
  - intros [H | [H | H]]; simpl in H; lra.
Qed.