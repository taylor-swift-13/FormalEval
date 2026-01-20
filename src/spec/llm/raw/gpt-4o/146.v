
Require Import List.
Require Import String.
Require Import Ascii.
Require Import ZArith.

Open Scope Z_scope.

Definition odd_digit (c : ascii) : Prop :=
  c = "1"%char \/ c = "3"%char \/ c = "5"%char \/ c = "7"%char \/ c = "9"%char.

Definition specialFilter_spec (nums : list Z) (count : Z) : Prop :=
  count = Z.of_nat (length (filter (fun num =>
    let num_str := Z.to_string num in
    Z.gt num 10 /\
    odd_digit (hd "0"%char (list_ascii_of_string num_str)) /\
    odd_digit (last (list_ascii_of_string num_str) "0"%char)
  ) nums)).
