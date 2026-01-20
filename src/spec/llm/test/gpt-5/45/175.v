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
  let input := [IZR 1000000000000%Z; 0.0008819244812954113%R] in
  let output := 440962240.6477056%R in
  match input with
  | a :: _ :: _ => triangle_area_spec a 0.0008819244812954112%R output
  | _ => False
  end.
Proof.
  simpl.
  unfold triangle_area_spec.
  replace (INR 2) with 2%R by reflexivity.
  replace (IZR 1000000000000) with 1000000000000%R by reflexivity.
  lra.
Qed.