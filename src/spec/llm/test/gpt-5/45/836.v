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
  let input_b := [true] in
  let input_r := [0.001%R] in
  let output := 0.0005%R in
  match input_b, input_r with
  | b :: _, h :: _ => triangle_area_spec (if b then 1%R else 0%R) h output
  | _, _ => False
  end.
Proof.
  simpl.
  unfold triangle_area_spec.
  replace (INR 2) with 2%R by reflexivity.
  simpl.
  lra.
Qed.