
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Definition string_sequence_spec (n : nat) (result : string) : Prop :=
  result = String.concat " " (map Nat.to_string (seq 0 (n + 1))).
