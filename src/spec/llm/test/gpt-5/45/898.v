Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Example triangle_area_test :
  let input := [549.9027289880141%R; 2.5%R] in
  let output := 687.378411235017625%R in
  match input with
  | a :: h :: _ => triangle_area_spec a h output
  | _ => False
  end.
Proof.
  simpl.
  unfold triangle_area_spec.
  replace (INR 2) with 2%R by reflexivity.
  lra.
Qed.