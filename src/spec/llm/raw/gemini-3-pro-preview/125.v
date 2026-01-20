
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.

Definition ord (c : ascii) : nat := nat_of_ascii c.

Definition is_whitespace (c : ascii) : bool :=
  match ord c with
  | 32 | 10 | 13 | 9 => true 
  | _ => false
  end.

Fixpoint string_exists (p : ascii -> bool) (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c s' => if p c then true else string_exists p s'
  end.

Definition contains_whitespace (s : string) : bool :=
  string_exists is_whitespace s.

Definition contains_comma (s : string) : bool :=
  string_exists (fun c => (c =? ",")%char) s.

Definition is_lower (c : ascii) : bool :=
  (97 <=? ord c) && (ord c <=? 122).

Definition is_odd_order (c : ascii) : bool :=
  Nat.odd (ord c - 97).

Definition count_criteria (c : ascii) : bool :=
  is_lower c && is_odd_order c.

Fixpoint count_matching_chars (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => 
      let n := count_matching_chars s' in
      if count_criteria c then 1 + n else n
  end.

Parameter python_split_whitespace : string -> list string.
Parameter python_split_comma : string -> list string.

Inductive split_words_res :=
  | ResList (l : list string)
  | ResCnt (n : nat).

Definition split_words_spec (txt : string) (res : split_words_res) : Prop :=
  if contains_whitespace txt then
    res = ResList (python_split_whitespace txt)
  else if contains_comma txt then
    res = ResList (python_split_comma txt)
  else
    res = ResCnt (count_matching_chars txt).
