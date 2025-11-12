
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition is_prime_hex_digit (c : ascii) : bool :=
  match c with
  | "2"%char => true
  | "3"%char => true
  | "5"%char => true
  | "7"%char => true
  | "B"%char => true
  | "D"%char => true
  | _ => false
  end.

Definition count_prime_hex_digits (num : string) (count : nat) : Prop :=
  count = List.length (filter is_prime_hex_digit (list_from_string num)).

(* Auxiliary function to convert string to list of ascii *)
Fixpoint list_from_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_from_string s'
  end.
