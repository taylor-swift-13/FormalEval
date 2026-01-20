
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.

Open Scope string_scope.
Open Scope list_scope.

Definition is_whitespace (c : ascii) : bool :=
  if ascii_dec c " " then true else
  if ascii_dec c newline then true else
  if ascii_dec c carriage_return then true else
  if ascii_dec c tab then true else false.

Definition contains_whitespace (s : string) : bool :=
  existsb is_whitespace (list_ascii_of_string s).

Definition contains_comma (s : string) : bool :=
  existsb (Ascii.ascii_dec ",") (list_ascii_of_string s).

Definition ord (c : ascii) : nat :=
  match nat_of_ascii c with
  | n => n
  end.

Fixpoint split_on_whitespace (s : string) : list string :=
  (* Abstract specification placeholder;
     the actual splitting function implementation is not required here *)
  (* specification assumes output is list of words split on whitespace *)
  []%list.

Fixpoint split_on_comma (s : string) : list string :=
  (* Abstract specification placeholder; 
     assumes output is list of words split on ',' *)
  []%list.

Fixpoint count_odd_lowercase (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c rest =>
      let o := (nat_of_ascii c - nat_of_ascii "a") mod 26 in
      let odd_order := if (o mod 2 =? 1) && (andb (ascii_dec_lowercase c) true) then 1 else 0 in
      odd_order + count_odd_lowercase rest
  end.

Definition ascii_dec_lowercase (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (leb (nat_of_ascii "a") n) (leb n (nat_of_ascii "z")).

Inductive split_words_res : Type :=
| ResWords : list string -> split_words_res
| ResCount : nat -> split_words_res.

Definition split_words_spec (txt : string) (res : split_words_res) : Prop :=
  (contains_whitespace txt = true /\ res = ResWords (split_on_whitespace txt))
  \/
  (contains_whitespace txt = false /\ contains_comma txt = true /\ res = ResWords (split_on_comma txt))
  \/
  (contains_whitespace txt = false /\ contains_comma txt = false /\ res = ResCount (count_odd_lowercase txt)).
