
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition string_sequence_spec (n : nat) (s : string) : Prop :=
  s = String.concat " " (map (fun x => string_of_nat x) (seq 0 (S n))).
