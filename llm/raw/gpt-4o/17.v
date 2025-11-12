
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.

Definition count_beats_spec (note : string) (beats : nat) : Prop :=
  (note = "o" -> beats = 4) /\
  (note = "o|" -> beats = 2) /\
  (note = ".|" -> beats = 1).

Definition parse_music_spec (music_string : string) (beats_list : list nat) : Prop :=
  (music_string = "" -> beats_list = []) /\
  (music_string <> "" ->
    exists notes : list string,
      String.split " " music_string = notes /\
      Forall2 count_beats_spec notes beats_list).
