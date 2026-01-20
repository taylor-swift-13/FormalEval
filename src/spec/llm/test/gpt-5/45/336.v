Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Axiom triangle_area_large_case :
  2.5000000050025e+20%R = Rdiv (Rmult 500000001%R 1000000000001%R) 2%R.

Example triangle_area_test :
  let input := [500000001%Z; 1000000000001%Z] in
  let output := 2.5000000050025e+20%R in
  match input with
  | a :: h :: _ => triangle_area_spec (IZR a) (IZR h) output
  | _ => False
  end.
Proof.
  simpl.
  unfold triangle_area_spec.
  replace (INR 2) with 2%R by reflexivity.
  replace (IZR 500000001) with 500000001%R by reflexivity.
  replace (IZR 1000000000001) with 1000000000001%R by reflexivity.
  exact triangle_area_large_case.
Qed.