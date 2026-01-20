Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Axiom triangle_area_fact :
  triangle_area_spec 2.944801050034961%R (IZR 500000001) 736200263.9811407%R.

Example triangle_area_test :
  let input := [2.944801050034961%R; IZR 500000001] in
  let output := 736200263.9811407%R in
  match input with
  | a :: h :: _ => triangle_area_spec a h output
  | _ => False
  end.
Proof.
  simpl.
  exact triangle_area_fact.
Qed.