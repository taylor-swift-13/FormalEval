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
  let input := [999999999998%Z; 999999999999%Z] in
  let output := Rdiv (Rmult (IZR 999999999998) (IZR 999999999999)) (INR 2) in
  match input with
  | a :: h :: _ => triangle_area_spec (IZR a) (IZR h) output
  | _ => False
  end.
Proof.
  simpl.
  unfold triangle_area_spec.
  reflexivity.
Qed.