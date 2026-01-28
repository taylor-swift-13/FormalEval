Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition triangle_area_spec (a : R) (h : R) (area : R) : Prop :=
  area = (a * h) / 2.

Example test_triangle_area : triangle_area_spec 0.09250267285921429 1000 46.251336429607145.
Proof.
  unfold triangle_area_spec.
  lra.
Qed.