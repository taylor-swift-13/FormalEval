Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Definition value_to_R (x : Z + bool) : R :=
  match x with
  | inl z => IZR z
  | inr b => if b then 1%R else 0%R
  end.

Example triangle_area_test :
  let input := [inl 5%Z; inr true] in
  let output := 2.5%R in
  match input with
  | a :: h :: _ => triangle_area_spec (value_to_R a) (value_to_R h) output
  | _ => False
  end.
Proof.
  simpl.
  unfold triangle_area_spec.
  simpl.
  replace (INR 2) with 2%R by reflexivity.
  replace (IZR 5) with 5%R by reflexivity.
  lra.
Qed.