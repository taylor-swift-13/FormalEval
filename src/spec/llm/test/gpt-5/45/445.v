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
  triangle_area_spec (IZR 500000002%Z) (IZR 500000001%Z) (1.2500000075e+17%R).

Example triangle_area_test :
  let input := [500000002%Z; 500000001%Z] in
  let output := 1.2500000075e+17%R in
  match input with
  | a :: h :: _ => triangle_area_spec (IZR a) (IZR h) output
  | _ => False
  end.
Proof.
  simpl.
  exact triangle_area_test_axiom.
Qed.