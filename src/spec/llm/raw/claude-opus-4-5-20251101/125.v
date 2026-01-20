
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Inductive split_result : Type :=
  | WordList : list string -> split_result
  | Count : nat -> split_result.

Definition is_whitespace (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (Nat.eqb n 32)
  (orb (Nat.eqb n 10)
  (orb (Nat.eqb n 13)
       (Nat.eqb n 9))).

Definition is_comma (c : ascii) : bool :=
  Nat.eqb (nat_of_ascii c) 44.

Definition is_lowercase (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (Nat.leb 97 n) (Nat.leb n 122).

Definition has_odd_order (c : ascii) : bool :=
  let n := nat_of_ascii c in
  Nat.odd (n - 97).

Fixpoint contains_char (s : string) (pred : ascii -> bool) : bool :=
  match s with
  | EmptyString => false
  | String c rest => orb (pred c) (contains_char rest pred)
  end.

Fixpoint count_odd_lowercase (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c rest =>
    if andb (is_lowercase c) (has_odd_order c)
    then S (count_odd_lowercase rest)
    else count_odd_lowercase rest
  end.

Definition contains_whitespace (s : string) : bool :=
  contains_char s is_whitespace.

Definition contains_comma (s : string) : bool :=
  contains_char s is_comma.

Parameter split_on_whitespace : string -> list string.
Parameter split_on_comma : string -> list string.

Definition split_words_spec (txt : string) (result : split_result) : Prop :=
  (contains_whitespace txt = true -> 
    exists ws, result = WordList ws /\ ws = split_on_whitespace txt) /\
  (contains_whitespace txt = false -> contains_comma txt = true ->
    exists ws, result = WordList ws /\ ws = split_on_comma txt) /\
  (contains_whitespace txt = false -> contains_comma txt = false ->
    result = Count (count_odd_lowercase txt)).
