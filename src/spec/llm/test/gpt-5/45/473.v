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
  let input := [2.2789244163895868%R; 2.968862381334059%R] in
  let output := 3.3829064848613597%R in
  match input with
  | a :: h :: _ :: _ => triangle_area_spec a h output
  | _ => True
  end.
Proof.
  simpl.
  trivial.
Qed.