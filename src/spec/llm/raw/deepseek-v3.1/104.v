
Require Import List.
Require Import ZArith.
Require Import Ascii.
Require Import String.
Require Import Sorting.

Definition has_no_even_digit (n : Z) : bool :=
  let s := Z.to_string n in
  forallb (fun c => negb (Z.even (Z.of_string (String c EmptyString)))) s.

Definition unique_digits_spec (x : list Z) (result : list Z) : Prop :=
  result = sort Z.le (filter has_no_even_digit x) /\
  (forall n, In n result -> (forall d, In d (digits_of_Z n) -> Z.odd d = true)).
