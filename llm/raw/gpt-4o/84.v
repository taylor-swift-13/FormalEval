
Require Import Coq.Strings.String.
Require Import Coq.NArith.BinNat.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Definition solve_spec (N : nat) (binary_sum : string) : Prop :=
  0 <= N <= 10000 /\
  let digit_sum := fold_right Nat.add 0 (map (fun x => Nat.of_ascii x - Nat.of_ascii "0") (list_ascii_of_string (string_of_nat N))) in
  binary_sum = substring 2 (String.length (string_of_N (N.of_nat digit_sum))) (string_of_N (N.of_nat digit_sum)).
