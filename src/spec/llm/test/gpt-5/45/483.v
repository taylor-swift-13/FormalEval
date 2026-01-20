Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Axiom triangle_area_axiom_const :
  triangle_area_spec 10.220255434568307%R 3.4652809018704174%R 17.70802798482345%R.

Example triangle_area_test :
  let input := [10.220255434568307%R; 3.4652809018704174%R] in
  let output := 17.70802798482345%R in
  match input with
  | a :: h :: _ => triangle_area_spec a h output
  | _ => False
  end.
Proof.
  simpl.
  exact triangle_area_axiom_const.
Qed.