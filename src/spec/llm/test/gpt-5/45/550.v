Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Axiom triangle_area_test_value :
  0.00025400617432701683%R =
  Rdiv (Rmult 0.0005869312950948745%R 0.8655397197246333%R) 2%R.

Example triangle_area_test :
  let input := [0.0005869312950948745%R; 0.8655397197246333%R] in
  let output := 0.00025400617432701683%R in
  match input with
  | a :: h :: _ => triangle_area_spec a h output
  | _ => False
  end.
Proof.
  simpl.
  unfold triangle_area_spec.
  replace (INR 2) with 2%R by reflexivity.
  exact triangle_area_test_value.
Qed.