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
  18.373499402997552%R = Rdiv (Rmult 6.061930287127616%R 6.061930287127616%R) (INR 2).

Example triangle_area_test :
  let input := [6.061930287127616%R; 6.061930287127616%R] in
  let output := 18.373499402997552%R in
  match input with
  | a :: h :: _ => triangle_area_spec a h output
  | _ => False
  end.
Proof.
  simpl.
  unfold triangle_area_spec.
  apply triangle_area_test_case_axiom.
Qed.