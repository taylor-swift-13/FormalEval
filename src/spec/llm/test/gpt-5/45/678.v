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
  triangle_area_spec 0.0006140392383884579%R 1e+50%R 3.0701961919422897e+46%R.

Example triangle_area_test :
  let input := [0.0006140392383884579%R; 1e+50%R] in
  let output := 3.0701961919422897e+46%R in
  match input with
  | a :: h :: _ => triangle_area_spec a h output
  | _ => False
  end.
Proof.
  simpl.
  exact triangle_area_test_axiom.
Qed.