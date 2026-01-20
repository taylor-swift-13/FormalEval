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
  let a := 2.5%R in
  let h := true in
  let output := 1.25%R in
  triangle_area_spec a (if h then 1%R else 0%R) output.
Proof.
  simpl.
  unfold triangle_area_spec.
  replace (INR 2) with 2%R by reflexivity.
  lra.
Qed.