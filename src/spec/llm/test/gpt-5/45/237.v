Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  Rabs (area - Rdiv (Rmult a h) (INR 2)) <= 0.00000000000000001%R.

Example triangle_area_test :
  let input := [2.5%R; 0.09250267285921429%R] in
  let output := 0.11562834107401787%R in
  match input with
  | a :: h :: _ => triangle_area_spec a h output
  | _ => False
  end.
Proof.
  simpl.
  unfold triangle_area_spec.
  replace (INR 2) with 2%R by reflexivity.
  apply Rabs_le.
  split; lra.
Qed.