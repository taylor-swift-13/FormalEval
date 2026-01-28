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

Fixpoint split_aux (s : string) (cur : string) : list string :=
  match s with
  | EmptyString => if string_dec cur "" then [] else [cur]
  | String c s' =>
      if string_dec (String c EmptyString) " " then
        if string_dec cur "" then split_aux s' ""
        else cur :: split_aux s' ""
      else split_aux s' (cur ++ String c EmptyString)
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

Example test_parse_music: parse_music_spec "o| o| o| .| o| .|" [2; 2; 2; 1; 2; 1].
Proof.
  unfold parse_music_spec.
  split.
  - intros H. inversion H.
  - intros _.
    simpl.
    split.
    + reflexivity.
    + intros i note beat Hn Hb.
      destruct i; simpl in Hn, Hb.
      * injection Hn as H1; injection Hb as H2; subst.
        right. left. split; reflexivity.
      * destruct i; simpl in Hn, Hb.
        { injection Hn as H1; injection Hb as H2; subst.
          right. left. split; reflexivity. }
        destruct i; simpl in Hn, Hb.
        { injection Hn as H1; injection Hb as H2; subst.
          right. left. split; reflexivity. }
        destruct i; simpl in Hn, Hb.
        { injection Hn as H1; injection Hb as H2; subst.
          right. right. split; reflexivity. }
        destruct i; simpl in Hn, Hb.
        { injection Hn as H1; injection Hb as H2; subst.
          right. left. split; reflexivity. }
        destruct i; simpl in Hn, Hb.
        { injection Hn as H1; injection Hb as H2; subst.
          right. right. split; reflexivity. }
        destruct i; inversion Hn.
Qed.