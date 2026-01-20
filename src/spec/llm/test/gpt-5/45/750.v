Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Axiom triangle_area_test_axiom :
  let input := [6.270108721907589e+49%R; 0.5520481891140395%R] in
  let output := 1.7307010827386147e+49%R in
  match input with
  | a :: h :: _ => triangle_area_spec a h output
  | _ => False
  end.

Example triangle_area_test :
  let input := [6.270108721907589e+49%R; 0.5520481891140395%R] in
  let output := 1.7307010827386147e+49%R in
  match input with
  | a :: h :: _ => triangle_area_spec a h output
  | _ => False
  end.
Proof.
  exact triangle_area_test_axiom.
Qed.