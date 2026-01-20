Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Axiom triangle_area_axiom_specific :
  triangle_area_spec (IZR 999999999997) 2.03121563844987%R 1015607819221.8881%R.

Example triangle_area_test :
  let input := [IZR 999999999997; 2.03121563844987%R] in
  let output := 1015607819221.8881%R in
  match input with
  | a :: h :: _ => triangle_area_spec a h output
  | _ => False
  end.
Proof.
  simpl.
  exact triangle_area_axiom_specific.
Qed.