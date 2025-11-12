
Require Import String.
Require Import List.
Require Import Ascii.
Require Import Bool.

Definition is_digit (c : ascii) : bool :=
  (c >= "0")%char && (c <= "9")%char.

Definition is_alpha (c : ascii) : bool :=
  ((c >= "a")%char && (c <= "z")%char) || ((c >= "A")%char && (c <= "Z")%char.

Definition count_digits (s : string) : nat :=
  length (filter (fun c => is_digit c) (list_ascii_of_string s)).

Definition valid_extensions : list string :=
  ["txt"; "exe"; "dll"].

Definition file_name_check_spec (file_name : string) (result : string) : Prop :=
  (count_digits file_name > 3 \/
   length (split "." file_name) <> 2 \/
   length (hd "" (split "." file_name)) = 0 \/
   negb (is_alpha (hd Null (list_ascii_of_string (hd "" (split "." file_name))))) \/
   ~In (last (split "." file_name) "") valid_extensions) /\ result = "No" \/
  ~(count_digits file_name > 3 \/
    length (split "." file_name) <> 2 \/
    length (hd "" (split "." file_name)) = 0 \/
    negb (is_alpha (hd Null (list_ascii_of_string (hd "" (split "." file_name))))) \/
    ~In (last (split "." file_name) "") valid_extensions) /\ result = "Yes".
