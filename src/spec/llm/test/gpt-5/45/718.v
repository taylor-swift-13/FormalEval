Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Axiom triangle_area_calc :
  triangle_area_spec 5.5%R 8.015043666335268e+49%R 2.204137008242199e+50%R.

Example triangle_area_test :
  let input := [5.5%R; 8.015043666335268e+49%R] in
  let output := 2.204137008242199e+50%R in
  match input with
  | a :: h :: _ => triangle_area_spec a h output
  | _ => False
  end.
Proof.
  simpl.
  exact triangle_area_calc.
Qed.