
Require Import String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

Definition decimal_to_binary_spec (decimal : nat) (binary_string : string) : Prop :=
  binary_string = "db" ++ substring 2 (String.length (bin_of_nat decimal)) (bin_of_nat decimal) ++ "db".
