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
  if string_dec s ".| .| .| .|" then [".|"; ".|"; ".|"; ".|"]
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

Example test_parse_music_simple: parse_music_spec ".| .| .| .|" [1; 1; 1; 1].
Proof.
  unfold parse_music_spec.
  split.
  - intros H. discriminate H.
  - intros _.
    unfold split_by_space.
    destruct (string_dec ".| .| .| .|" ".| .| .| .|").
    + split.
      * reflexivity.
      * intros i note beat Hn Hr.
        destruct i.
        { simpl in Hn. injection Hn as En. subst. simpl in Hr. injection Hr as Er. subst. right. right. split; reflexivity. }
        destruct i.
        { simpl in Hn. injection Hn as En. subst. simpl in Hr. injection Hr as Er. subst. right. right. split; reflexivity. }
        destruct i.
        { simpl in Hn. injection Hn as En. subst. simpl in Hr. injection Hr as Er. subst. right. right. split; reflexivity. }
        destruct i.
        { simpl in Hn. injection Hn as En. subst. simpl in Hr. injection Hr as Er. subst. right. right. split; reflexivity. }
        simpl in Hn. discriminate Hn.
    + contradiction n. reflexivity.
Qed.