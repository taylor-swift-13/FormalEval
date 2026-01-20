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
  triangle_area_spec (IZR 1000000000001%Z) (IZR 1000000000002%Z) (5.000000000015e+23%R).

Example triangle_area_test :
  let input := [1000000000001%Z; 1000000000002%Z] in
  let output := 5.000000000015e+23%R in
  match input with
  | a :: h :: _ => triangle_area_spec (IZR a) (IZR h) output
  | _ => False
  end.
Proof.
  simpl.
  exact triangle_area_test_axiom.
Qed.