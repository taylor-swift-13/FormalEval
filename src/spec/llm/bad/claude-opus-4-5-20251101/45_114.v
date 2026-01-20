Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition triangle_area_spec (a : R) (h : R) (area : R) : Prop :=
  area = (a * h) / 2.

Example triangle_area_test : triangle_area_spec 2.5171570275185937 4 5.034314055037187.
Proof.
  unfold triangle_area_spec.
  unfold Rdiv.
  ring_simplify.
  reflexivity.
Qed.