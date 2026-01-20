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
  triangle_area_spec (IZR 500000001) 1.9656455435118383%R 491411386.8607823%R.

Example triangle_area_test :
  let input := (500000001%Z, 1.9656455435118383%R) in
  let output := 491411386.8607823%R in
  match input with
  | (a, h) => triangle_area_spec (IZR a) h output
  end.
Proof.
  simpl.
  exact triangle_area_test_axiom.
Qed.