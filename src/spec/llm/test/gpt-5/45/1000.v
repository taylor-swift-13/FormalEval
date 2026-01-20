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
  let input := [3.71357594772759%R; 3.5%R] in
  let output := 6.498757908523282%R in
  match input with
  | a :: h :: _ :: _ => triangle_area_spec a h output
  | _ => True
  end.
Proof.
  simpl.
  exact I.
Qed.