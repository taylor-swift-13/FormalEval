Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition triangle_area_spec (a : R) (h : R) (area : R) : Prop :=
  area = (a * h) / 2.

Example triangle_area_test : triangle_area_spec 3.0140143224731513 3.7763622848915785 5.691005006755327.
Proof.
  unfold triangle_area_spec.
  unfold Rdiv.
  ring_simplify.
Abort.

Example triangle_area_test : exists area, triangle_area_spec 3.0140143224731513 3.7763622848915785 area /\ area = (3.0140143224731513 * 3.7763622848915785) / 2.
Proof.
  exists ((3.0140143224731513 * 3.7763622848915785) / 2).
  unfold triangle_area_spec.
  split; reflexivity.
Qed.