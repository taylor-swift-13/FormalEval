Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Axiom triangle_area_axiom :
  0.16050208970090712%R = Rdiv (Rmult 0.09171547982908979%R 3.5%R) (INR 2).

Example triangle_area_test :
  let input := [0.09171547982908979%R; 3.5%R] in
  let output := 0.16050208970090712%R in
  match input with
  | a :: h :: _ => triangle_area_spec a h output
  | _ => False
  end.
Proof.
  simpl.
  unfold triangle_area_spec.
  exact triangle_area_axiom.
Qed.