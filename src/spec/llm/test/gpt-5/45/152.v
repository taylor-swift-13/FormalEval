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
  let input := [inl 2.944801050034961%R; inr 1000000000000%Z] in
  let output := 1472400525017.4805%R in
  match input with
  | inl a :: inr h :: _ => triangle_area_spec a (IZR h) output
  | _ => False
  end.
Proof.
  simpl.
  unfold triangle_area_spec.
  replace (INR 2) with 2%R by reflexivity.
  replace (IZR 1000000000000) with 1000000000000%R by reflexivity.
  lra.
Qed.