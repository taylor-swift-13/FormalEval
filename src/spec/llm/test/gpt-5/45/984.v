Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Axiom triangle_area_new_test_eq :
  81700.28119023451%R = Rdiv (Rmult 1000.234%R 163.36233559394003%R) (INR 2).

Example triangle_area_test :
  let input := [1000.234%R; 163.36233559394003%R] in
  let output := 81700.28119023451%R in
  match input with
  | a :: h :: _ => triangle_area_spec a h output
  | _ => False
  end.
Proof.
  simpl.
  unfold triangle_area_spec.
  apply triangle_area_new_test_eq.
Qed.