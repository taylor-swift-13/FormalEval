
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.ListSet.

Definition is_odd_digit (ch : ascii) : bool :=
  negb (Nat.even (nat_of_ascii ch)).

Definition judge (n : nat) : bool :=
  forallb is_odd_digit (string_of_nat n).

Definition unique_digits_spec (x : list nat) (result : list nat) : Prop :=
  result = sort Nat.leb (filter judge x).
