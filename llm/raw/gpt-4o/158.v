
Require Import List.
Require Import String.
Require Import Ascii.
Require Import PeanoNat.
Import ListNotations.

Definition unique_chars_count (s : string) : nat :=
  length (nodup ascii_dec (list_ascii_of_string s)).

Definition find_max_spec (words : list string) (result : string) : Prop :=
  In result words /\
  (forall word, In word words -> unique_chars_count word <= unique_chars_count result) /\
  (forall word, In word words -> unique_chars_count word = unique_chars_count result -> word >= result).
