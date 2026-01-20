Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Inductive input_elem :=
| RInput (r : R)
| ZInput (z : Z).

Axiom triangle_area_fact :
  triangle_area_spec 0.000804346648273894%R (IZR 1001) 0.40257549746108395%R.

Example triangle_area_test :
  let input := [RInput 0.000804346648273894%R; ZInput 1001%Z] in
  let output := 0.40257549746108395%R in
  match input with
  | RInput a :: ZInput h :: _ => triangle_area_spec a (IZR h) output
  | _ => False
  end.
Proof.
  simpl.
  exact triangle_area_fact.
Qed.