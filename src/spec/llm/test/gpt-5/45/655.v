Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Example triangle_area_test :
  let a := 1000.234%R in
  let h := 1000%Z in
  let output := 500117.0%R in
  triangle_area_spec a (IZR h) output.
Proof.
  simpl.
  unfold triangle_area_spec.
  replace (INR 2) with 2%R by reflexivity.
  replace (IZR 1000) with 1000%R by reflexivity.
  lra.
Qed.