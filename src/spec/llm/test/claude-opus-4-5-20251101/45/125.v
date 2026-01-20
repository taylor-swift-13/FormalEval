Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition triangle_area_spec (a : R) (h : R) (area : R) : Prop :=
  area = (a * h) / 2.

Example triangle_area_test : triangle_area_spec 3.0140143224731513 3.0140143224731513 4.542141168036644.
Proof.
  unfold triangle_area_spec.
  unfold Rdiv.
  ring_simplify.
Abort.

Example triangle_area_test : exists area : R, triangle_area_spec 3.0140143224731513 3.0140143224731513 area /\ area = (3.0140143224731513 * 3.0140143224731513) / 2.
Proof.
  exists ((3.0140143224731513 * 3.0140143224731513) / 2).
  unfold triangle_area_spec.
  split; reflexivity.
Qed.