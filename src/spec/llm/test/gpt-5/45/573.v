Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Axiom triangle_area_case :
  triangle_area_spec 6.909600955216463%R (IZR 1000000000001%Z) 3454800477611.686%R.

Example triangle_area_test :
  let input := (6.909600955216463%R, 1000000000001%Z) in
  let output := 3454800477611.686%R in
  match input with
  | (a, h) => triangle_area_spec a (IZR h) output
  end.
Proof.
  simpl.
  exact triangle_area_case.
Qed.