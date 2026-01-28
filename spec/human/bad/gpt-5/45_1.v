Require Import Reals.
Require Import Lra.
Require Import ZArith.
Require Import List.

Open Scope R_scope.
Open Scope Z_scope.

(* Pre: side and high should be non-negative for a valid triangle area *)
Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
  output = side * high / 2.

Example problem_45_test :
  let input : list Z := (5%Z :: 3%Z :: nil) in
  let side : R := 5%R in
  let high : R := 3%R in
  let output : R := 7.5%R in
  problem_45_pre side high /\ problem_45_spec side high output.
Proof.
  simpl.
  split.
  - unfold problem_45_pre. split; lra.
  - unfold problem_45_spec. lra.
Qed.