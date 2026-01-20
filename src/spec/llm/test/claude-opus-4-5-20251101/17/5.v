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

Fixpoint split_by_space (s : string) : list string :=
  match s with
  | EmptyString => []
  | _ => []
  end.

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

Definition parse_music_spec' (music_string : string) (notes : list string) (result : list Z) : Prop :=
  length result = length notes /\
  forall i note beat,
    nth_error notes i = Some note ->
    nth_error result i = Some beat ->
    ((note = "o" /\ beat = 4) \/
     (note = "o|" /\ beat = 2) \/
     (note = ".|" /\ beat = 1)).

Example parse_music_test_main : 
  parse_music_spec' "o| .| o| .| o o| o o|" 
                    ["o|"; ".|"; "o|"; ".|"; "o"; "o|"; "o"; "o|"]
                    [2%Z; 1%Z; 2%Z; 1%Z; 4%Z; 2%Z; 4%Z; 2%Z].
Proof.
  unfold parse_music_spec'.
  split.
  - reflexivity.
  - intros i note beat Hnote Hbeat.
    destruct i as [|[|[|[|[|[|[|[|i']]]]]]]].
    + simpl in Hnote, Hbeat.
      injection Hnote as Hnote.
      injection Hbeat as Hbeat.
      right. left. split; symmetry; assumption.
    + simpl in Hnote, Hbeat.
      injection Hnote as Hnote.
      injection Hbeat as Hbeat.
      right. right. split; symmetry; assumption.
    + simpl in Hnote, Hbeat.
      injection Hnote as Hnote.
      injection Hbeat as Hbeat.
      right. left. split; symmetry; assumption.
    + simpl in Hnote, Hbeat.
      injection Hnote as Hnote.
      injection Hbeat as Hbeat.
      right. right. split; symmetry; assumption.
    + simpl in Hnote, Hbeat.
      injection Hnote as Hnote.
      injection Hbeat as Hbeat.
      left. split; symmetry; assumption.
    + simpl in Hnote, Hbeat.
      injection Hnote as Hnote.
      injection Hbeat as Hbeat.
      right. left. split; symmetry; assumption.
    + simpl in Hnote, Hbeat.
      injection Hnote as Hnote.
      injection Hbeat as Hbeat.
      left. split; symmetry; assumption.
    + simpl in Hnote, Hbeat.
      injection Hnote as Hnote.
      injection Hbeat as Hbeat.
      right. left. split; symmetry; assumption.
    + simpl in Hnote, Hbeat.
      destruct i'; discriminate Hnote.
Qed.