Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Axiom triangle_area_test_case_axiom :
  4.0075218331676345e+99%R = Rdiv (Rmult 1e+50%R 8.015043666335268e+49%R) 2%R.

Example triangle_area_test :
  let input := [1e+50%R; 8.015043666335268e+49%R] in
  let output := 4.0075218331676345e+99%R in
  match input with
  | a :: h :: _ => triangle_area_spec a h output
  | _ => False
  end.
Proof.
  simpl.
  unfold triangle_area_spec.
  replace (INR 2) with 2%R by reflexivity.
  exact triangle_area_test_case_axiom.
Qed.