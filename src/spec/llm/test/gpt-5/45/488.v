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
  let input := [2.312809121647276%R; 2.5171570275185937%R] in
  let output := 2.9108518669317736%R in
  exists area,
  match input with
  | a :: h :: _ => triangle_area_spec a h area
  | _ => False
  end.
Proof.
  simpl.
  exists (Rdiv (Rmult 2.312809121647276 2.5171570275185937) (INR 2)).
  unfold triangle_area_spec.
  reflexivity.
Qed.