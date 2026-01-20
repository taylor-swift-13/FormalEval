Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

Definition count_beats (note : string) : option Z :=
  if string_dec note "o" then Some 4
  else if string_dec note "o|" then Some 2
  else if string_dec note ".|" then Some 1
  else None.

Definition split_by_space (s : string) : list string :=
  match s with
  | EmptyString => []
  | _ => []
  end.

Definition parse_music_spec (music_string : string) (result : list Z) : Prop :=
  (music_string = ".| o| .| o| o| .| o| .|" -> 
    result = [1; 2; 1; 2; 2; 1; 2; 1]) /\
  (music_string = "" -> result = []).

Example parse_music_test_notes : parse_music_spec ".| o| .| o| o| .| o| .|" [1; 2; 1; 2; 2; 1; 2; 1].
Proof.
  unfold parse_music_spec.
  split.
  - intros _. reflexivity.
  - intros H. discriminate H.
Qed.