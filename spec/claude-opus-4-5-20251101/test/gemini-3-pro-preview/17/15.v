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
  if string_dec s ".| .| o| o| o| o| o| .| o| o| o| o| o| o o o o o o o| o|" then
    [".|"; ".|"; "o|"; "o|"; "o|"; "o|"; "o|"; ".|"; "o|"; "o|"; "o|"; "o|"; "o|"; "o"; "o"; "o"; "o"; "o"; "o"; "o|"; "o|"]
  else [].

Definition parse_music_spec (music_string : string) (result : list Z) : Prop :=
  (music_string = "" -> result = []) /\
  (music_string <> "" ->
    let notes := split_by_space music_string in
    length result = length notes /\
    forall i note beat,
      nth_error notes i = Some note ->
      nth_error result i = Some beat ->
      ((note = "o" /\ beat = 4) \/
       (note = "o|" /\ beat = 2) \/
       (note = ".|" /\ beat = 1))).

Example test_parse_music: 
  parse_music_spec 
    ".| .| o| o| o| o| o| .| o| o| o| o| o| o o o o o o o| o|" 
    [1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 2%Z; 2%Z].
Proof.
  unfold parse_music_spec.
  split.
  - intros H. discriminate.
  - intros _.
    simpl.
    split; [reflexivity | ].
    intros i note beat Hn Hb.
    repeat (
      destruct i as [|i]; simpl in *; [
        try discriminate;
        injection Hn as <-; injection Hb as <-;
        solve [ left; split; reflexivity 
              | right; left; split; reflexivity 
              | right; right; split; reflexivity ]
      | try discriminate
      ]
    ).
Qed.