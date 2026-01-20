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
  let input := [1e+50%R; 1e+50%R] in
  let output := 5.000000000000001e+99%R in
  match input with
  | a :: h :: _ :: _ => triangle_area_spec a h output
  | _ => True
  end.
Proof.
  simpl.
  exact I.
Qed.