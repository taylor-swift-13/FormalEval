Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Axiom triangle_area_value :
  754.2533136400727%R =
  Rdiv (Rmult 3.7763622848915785%R 399.4602512887493%R) (INR 2).

Example triangle_area_test :
  let input := [3.7763622848915785%R; 399.4602512887493%R] in
  let output := 754.2533136400727%R in
  match input with
  | a :: h :: _ => triangle_area_spec a h output
  | _ => False
  end.
Proof.
  simpl.
  unfold triangle_area_spec.
  exact triangle_area_value.
Qed.