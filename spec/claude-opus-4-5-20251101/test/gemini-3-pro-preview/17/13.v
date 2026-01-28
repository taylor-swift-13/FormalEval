Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
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

Fixpoint split_aux (s : string) (cur : string) : list string :=
  match s with
  | EmptyString => if string_dec cur "" then [] else [cur]
  | String c rest =>
      if ascii_dec c " " then
        if string_dec cur "" then split_aux rest ""
        else cur :: split_aux rest ""
      else split_aux rest (cur ++ String c EmptyString)
  end.

Definition split_by_space (s : string) : list string :=
  split_aux s "".

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

Example test_parse_music_custom: 
  parse_music_spec ".| o| .| o| o| .| o| .|" [1; 2; 1; 2; 2; 1; 2; 1].
Proof.
  unfold parse_music_spec.
  split.
  - intros H. discriminate.
  - intros _.
    split.
    + reflexivity.
    + intros i note beat Hn Hb.
      destruct i; simpl in Hn, Hb.
      { injection Hn as ->. injection Hb as ->. right; right; split; reflexivity. }
      destruct i; simpl in Hn, Hb.
      { injection Hn as ->. injection Hb as ->. right; left; split; reflexivity. }
      destruct i; simpl in Hn, Hb.
      { injection Hn as ->. injection Hb as ->. right; right; split; reflexivity. }
      destruct i; simpl in Hn, Hb.
      { injection Hn as ->. injection Hb as ->. right; left; split; reflexivity. }
      destruct i; simpl in Hn, Hb.
      { injection Hn as ->. injection Hb as ->. right; left; split; reflexivity. }
      destruct i; simpl in Hn, Hb.
      { injection Hn as ->. injection Hb as ->. right; right; split; reflexivity. }
      destruct i; simpl in Hn, Hb.
      { injection Hn as ->. injection Hb as ->. right; left; split; reflexivity. }
      destruct i; simpl in Hn, Hb.
      { injection Hn as ->. injection Hb as ->. right; right; split; reflexivity. }
      destruct i; discriminate.
Qed.