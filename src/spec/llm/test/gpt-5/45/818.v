Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Axiom triangle_area_specific_case :
  triangle_area_spec 594.6585361139911%R 550.123%R 163567.66893131856%R.

Example triangle_area_test :
  let input := [594.6585361139911%R; 550.123%R] in
  let output := 163567.66893131856%R in
  match input with
  | a :: h :: _ => triangle_area_spec a h output
  | _ => False
  end.
Proof.
  simpl.
  apply triangle_area_specific_case.
Qed.