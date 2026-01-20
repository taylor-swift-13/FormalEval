
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Import ListNotations.

Fixpoint all_lowercase_keys (l : list string) : bool :=
  match l with
  | [] => true
  | k :: ks => 
      if (forallb (fun c => 
        if (andb (negb (ascii_uppercase c)) (ascii_lowercase c)) then true else false) 
        (string_to_list k))
      then all_lowercase_keys ks
      else false
  end.

Fixpoint all_uppercase_keys (l : list string) : bool :=
  match l with
  | [] => true
  | k :: ks => 
      if (forallb (fun c => 
        if (andb (ascii_uppercase c) (negb (ascii_lowercase c))) then true else false) 
        (string_to_list k))
      then all_uppercase_keys ks
      else false
  end.

(* As the above ascii predicates do not exist in standard Coq, and string_to_list is to get chars from string, 
   we need a more abstract approach to define the property. 
   Instead, we define predicates on strings: is_lowercase and is_uppercase *)

Fixpoint is_lowercase_char (c : ascii) : bool :=
  match c with
  | "a" => true | "b" => true | "c" => true | "d" => true | "e" => true
  | "f" => true | "g" => true | "h" => true | "i" => true | "j" => true
  | "k" => true | "l" => true | "m" => true | "n" => true | "o" => true
  | "p" => true | "q" => true | "r" => true | "s" => true | "t" => true
  | "u" => true | "v" => true | "w" => true | "x" => true | "y" => true | "z" => true
  | _ => false
  end.

Fixpoint is_uppercase_char (c : ascii) : bool :=
  match c with
  | "A" => true | "B" => true | "C" => true | "D" => true | "E" => true
  | "F" => true | "G" => true | "H" => true | "I" => true | "J" => true
  | "K" => true | "L" => true | "M" => true | "N" => true | "O" => true
  | "P" => true | "Q" => true | "R" => true | "S" => true | "T" => true
  | "U" => true | "V" => true | "W" => true | "X" => true | "Y" => true | "Z" => true
  | _ => false
  end.

Fixpoint all_chars_lowercase (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c rest => 
      andb (is_lowercase_char c) (all_chars_lowercase rest)
  end.

Fixpoint all_chars_uppercase (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c rest =>
      andb (is_uppercase_char c) (all_chars_uppercase rest)
  end.

Fixpoint all_keys_lowercase (l : list string) : bool :=
  match l with
  | [] => true
  | k :: ks =>
      if all_chars_lowercase k then all_keys_lowercase ks else false
  end.

Fixpoint all_keys_uppercase (l : list string) : bool :=
  match l with
  | [] => true
  | k :: ks =>
      if all_chars_uppercase k then all_keys_uppercase ks else false
  end.

Definition dict_key_type_string (keys : list (string + nat)) : Prop :=
  Forall (fun k => match k with
                  | inl _ => True
                  | _ => False
                  end) keys.

(* Since the input dictionary keys come from a dictionary that can have keys of mixed types, 
   we abstract by defining a predicate that keys are all strings.
   We model key as sum type (string + nat) for generality.
   But the problem only cares about keys that are strings; if any key is not a string, return False. *)

Definition check_dict_case_spec (keys : list string) (res : bool) : Prop :=
  keys <> [] /\
  ( (all_keys_lowercase keys = true /\ res = true)
    \/
    (all_keys_uppercase keys = true /\ res = true)
    \/
    (all_keys_lowercase keys = false /\ all_keys_uppercase keys = false /\ res = false)
  ).

(* Since Coq does not have native dictionary or mixed-type keys, 
   the predicate is specified as a property of keys list and the result boolean *)

