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
  let input := [2.607199296199486%R; 10.5%R] in
  let output := 13.6877963050473%R in
  match input with
  | a :: h :: _ => exists area, triangle_area_spec a h area
  | _ => False
  end.
Proof.
  simpl.
  eexists.
  unfold triangle_area_spec.
  reflexivity.
Qed.