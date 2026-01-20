Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Axiom triangle_area_eval :
  triangle_area_spec 1.2769285921500888%R (IZR 999999999999) 638464296074.4059%R.

Example triangle_area_test :
  let input := [1.2769285921500888%R; IZR 999999999999] in
  let output := 638464296074.4059%R in
  match input with
  | a :: h :: _ => triangle_area_spec a h output
  | _ => False
  end.
Proof.
  simpl.
  exact triangle_area_eval.
Qed.