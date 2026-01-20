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
  let input := [0.38843387915427663%R; 0.00000000000000000000000000000000000000000000000001%R] in
  let output := Rdiv (Rmult 0.38843387915427663%R 0.00000000000000000000000000000000000000000000000001%R) (INR 2) in
  match input with
  | a :: h :: _ => triangle_area_spec a h output
  | _ => False
  end.
Proof.
  simpl.
  unfold triangle_area_spec.
  reflexivity.
Qed.