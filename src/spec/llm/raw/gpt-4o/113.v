
Require Import List.
Require Import String.
Require Import Ascii.
Require Import Arith.
Import ListNotations.

Definition is_odd (ch : ascii) : bool :=
  match ch with
  | "0"%char => false
  | "1"%char => true
  | "2"%char => false
  | "3"%char => true
  | "4"%char => false
  | "5"%char => true
  | "6"%char => false
  | "7"%char => true
  | "8"%char => false
  | "9"%char => true
  | _ => false
  end.

Definition count_odd_digits (s : string) : nat :=
  length (filter is_odd (list_ascii_of_string s)).

Definition odd_count_spec (lst : list string) (ans : list string) : Prop :=
  ans = map (fun s =>
    let odd_cnt := count_odd_digits s in
    let template := "the number of odd elements in the string i of the input."%string in
    string_replace "i" (string_of_nat odd_cnt) template
  ) lst.
