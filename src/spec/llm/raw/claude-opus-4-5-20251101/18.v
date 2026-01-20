
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => nil
  | String c rest => c :: string_to_list rest
  end.

Fixpoint list_to_string (l : list ascii) : string :=
  match l with
  | nil => EmptyString
  | c :: rest => String c (list_to_string rest)
  end.

Fixpoint string_prefix (pre s : string) : bool :=
  match pre, s with
  | EmptyString, _ => true
  | String c1 rest1, String c2 rest2 =>
      if Ascii.eqb c1 c2 then string_prefix rest1 rest2 else false
  | _, EmptyString => false
  end.

Fixpoint string_length (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String _ rest => S (string_length rest)
  end.

Fixpoint substring_from (s : string) (n : nat) : string :=
  match n, s with
  | 0, _ => s
  | S m, EmptyString => EmptyString
  | S m, String _ rest => substring_from rest m
  end.

Fixpoint count_occurrences_aux (s substring : string) (pos remaining : nat) : nat :=
  match remaining with
  | 0 => 0
  | S rem =>
      let suffix := substring_from s pos in
      let count_here := if string_prefix substring suffix then 1 else 0 in
      count_here + count_occurrences_aux s substring (S pos) rem
  end.

Definition count_occurrences (s substring : string) : nat :=
  count_occurrences_aux s substring 0 (string_length s).

Definition how_many_times_spec (s : string) (substring : string) (result : nat) : Prop :=
  result = count_occurrences s substring.
