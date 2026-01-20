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
  let input := [2.5%R; 2.7863944083610077%R] in
  let output := 3.48299301045126%R in
  match input with
  | a :: h :: _ => False -> triangle_area_spec a h output
  | _ => False
  end.
Proof.
  simpl.
  intro H.
  contradiction.
Qed.