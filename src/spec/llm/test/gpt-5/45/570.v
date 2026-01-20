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
  let input := [5.594645686633063%R; 5.594645686633063%R] in
  let output := 15.65003017948097%R in
  match input with
  | a :: h :: _ => triangle_area_spec a h (Rdiv (Rmult a h) (INR 2))
  | _ => False
  end.
Proof.
  simpl.
  unfold triangle_area_spec.
  reflexivity.
Qed.