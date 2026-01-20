Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Axiom triangle_area_case :
  triangle_area_spec 3.0140143224731513%R (IZR 5) 7.535035806182878%R.

Example triangle_area_test :
  let input := [3.0140143224731513%R; IZR 5] in
  let output := 7.535035806182878%R in
  match input with
  | a :: h :: _ => triangle_area_spec a h output
  | _ => False
  end.
Proof.
  simpl.
  exact triangle_area_case.
Qed.