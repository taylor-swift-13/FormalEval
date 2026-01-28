Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition triangle_area_spec (a : R) (h : R) (area : R) : Prop :=
  area = (a * h) / 2.

Example test_triangle_area : triangle_area_spec (powerRZ 10 (-50)%Z) (powerRZ 10 50%Z) 0.5.
Proof.
  unfold triangle_area_spec.
  rewrite <- powerRZ_add; [|lra].
  replace (-50 + 50)%Z with 0%Z by reflexivity.
  simpl.
  lra.
Qed.