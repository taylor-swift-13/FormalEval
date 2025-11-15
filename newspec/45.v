(* Given length of a side and high return area for a triangle.
>>> triangle_area(5, 3)
7.5 *)

(* Spec(side : float, high : float, output : float) :=
	output = side * high / 2 *)

Require Import Reals.
Open Scope R_scope.

Definition Spec(side high output : R) : Prop :=
  output = side * high / 2.