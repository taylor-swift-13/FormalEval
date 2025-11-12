
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.

Definition compare_one_spec (a b : string) (result : option string) : Prop :=
  let num_a := float_of_string (replace "," "." a) in
  let num_b := float_of_string (replace "," "." b) in
  (num_a = num_b -> result = None) /\
  (num_a > num_b -> result = Some a) /\
  (num_a < num_b -> result = Some b).
