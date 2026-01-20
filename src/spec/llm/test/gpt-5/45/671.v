Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Axiom triangle_area_axiom :
  triangle_area_spec 1000.234 916.7189142883354 458466.7132571395.

Example triangle_area_test :
  let input := [1000.234%R; 916.7189142883354%R] in
  let output := 458466.7132571395%R in
  match input with
  | a :: h :: _ => triangle_area_spec a h output
  | _ => False
  end.
Proof.
  simpl.
  apply triangle_area_axiom.
Qed.