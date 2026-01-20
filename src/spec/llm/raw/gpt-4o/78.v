
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Bool.Bool.

Definition hex_key_spec (num : string) (count : nat) : Prop :=
  count = length (filter (fun x => In x ["2"; "3"; "5"; "7"; "B"; "D"]) (list_of_string num)).
