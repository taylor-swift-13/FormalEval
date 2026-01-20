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
  let input := (2.5171570275185937%R, 500000001%Z) in
  let output := Rdiv (Rmult (fst input) (IZR (snd input))) (INR 2) in
  match input with
  | (a, h) => triangle_area_spec a (IZR h) output
  end.
Proof.
  simpl.
  unfold triangle_area_spec.
  reflexivity.
Qed.