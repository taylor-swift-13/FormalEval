
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

(* Helper function to check for space character (ASCII 32) *)
Definition is_space (c : ascii) : bool :=
  Nat.eqb (nat_of_ascii c) 32.

(* Helper function to split a string by spaces *)
Fixpoint split_aux (s : string) (acc : string) : list string :=
  match s with
  | EmptyString => [acc]
  | String c s' =>
      if is_space c then
        acc :: split_aux s' EmptyString
      else
        split_aux s' (acc ++ String c EmptyString)
  end.

Definition split_by_space (s : string) : list string :=
  split_aux s EmptyString.

(* Helper function to join a list of strings with spaces *)
Fixpoint join_by_space (l : list string) : string :=
  match l with
  | [] => EmptyString
  | [w] => w
  | w :: ws => w ++ " " ++ join_by_space ws
  end.

(* Helper function to check if a number is prime *)
Fixpoint check_divisors (n : nat) (d : nat) : bool :=
  match d with
  | 0 | 1 => true
  | S d' => if (n mod d =? 0) then false else check_divisors n d'
  end.

Definition is_prime (n : nat) : bool :=
  if n <? 2 then false else check_divisors n (pred n).

(* Main Specification *)
Definition words_in_sentence_spec (sentence : string) (result : string) : Prop :=
  let words := split_by_space sentence in
  let filtered_words := filter (fun w => is_prime (String.length w)) words in
  result = join_by_space filtered_words.
