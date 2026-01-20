Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  Rabs (area - Rdiv (Rmult a h) (INR 2)) <= 0.000000000000000002%R.

Example triangle_area_test :
  let input := [0.1%R; 0.1%R] in
  let output := 0.005000000000000001%R in
  match input with
  | a :: h :: _ => triangle_area_spec a h output
  | _ => False
  end.
Proof.
  simpl.
  unfold triangle_area_spec.
  replace (INR 2) with 2%R by reflexivity.
  apply Rabs_le; split; lra.
Qed.