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
  let input := [inl true; inr 10%Z] in
  let output := 5.0%R in
  match input with
  | inl b :: inr z :: _ => triangle_area_spec (if b then 1%R else 0%R) (IZR z) output
  | _ => False
  end.
Proof.
  simpl.
  unfold triangle_area_spec.
  replace (INR 2) with 2%R by reflexivity.
  replace (IZR 10) with 10%R by reflexivity.
  lra.
Qed.