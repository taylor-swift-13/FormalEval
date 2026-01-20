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
  let input := (11.15441836003326%R, true) in
  let output := 5.57720918001663%R in
  match input with
  | (a, b) => triangle_area_spec a (if b then 1%R else 0%R) output
  end.
Proof.
  simpl.
  unfold triangle_area_spec.
  replace (INR 2) with 2%R by reflexivity.
  lra.
Qed.