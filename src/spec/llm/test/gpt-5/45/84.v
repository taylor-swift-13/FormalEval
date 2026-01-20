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
  let input := [29%Z; 13%Z] in
  let output := 188.5%R in
  match input with
  | a :: h :: _ => triangle_area_spec (IZR a) (IZR h) output
  | _ => False
  end.
Proof.
  simpl.
  unfold triangle_area_spec.
  replace (INR 2) with 2%R by reflexivity.
  replace (IZR 29) with 29%R by reflexivity.
  replace (IZR 13) with 13%R by reflexivity.
  lra.
Qed.