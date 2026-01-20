
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

Definition count_distinct_characters_spec (s : string) (count : nat) : Prop :=
  exists (distinct_chars : list ascii),
    NoDup distinct_chars /\
    (forall c, In c distinct_chars <-> In c (map Ascii.to_lower (list_ascii_of_string s))) /\
    count = length distinct_chars.
