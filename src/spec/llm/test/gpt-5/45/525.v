Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Axiom triangle_area_exact :
  triangle_area_spec 0.562579842154142%R 4.0666300912371804%R 1.1439020574137486%R.

Example triangle_area_test :
  let input := [0.562579842154142%R; 4.0666300912371804%R] in
  let output := 1.1439020574137486%R in
  match input with
  | a :: h :: _ => triangle_area_spec a h output
  | _ => False
  end.
Proof.
  simpl.
  exact triangle_area_exact.
Qed.