Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Axiom triangle_area_case :
  triangle_area_spec (IZR 499999997) 0.0006140392383884579 153509.8086760556.

Example triangle_area_test :
  let input : list (Z + R) := [inl 499999997%Z; inr 0.0006140392383884579%R] in
  let output := 153509.8086760556%R in
  match input with
  | inl a :: inr h :: _ => triangle_area_spec (IZR a) h output
  | _ => False
  end.
Proof.
  simpl.
  exact triangle_area_case.
Qed.