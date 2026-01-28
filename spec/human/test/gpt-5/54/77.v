Require Import List Ascii String.
Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.

Definition problem_54_pre (s0 s1 : string) : Prop := True.

Definition problem_54_spec (s0 s1 : string) (b : bool) : Prop :=
  let list_s0 := list_ascii_of_string s0 in
  let list_s1 := list_ascii_of_string s1 in
  b = true <-> (forall (c : ascii), In c list_s0 <-> In c list_s1).

Example problem_54_test_example :
  problem_54_spec "abde" "abcde" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. exfalso. discriminate H.
  - intros Hall.
    specialize (Hall "c").
    simpl in Hall.
    destruct Hall as [Hlr Hrl].
    assert (Hin_right : In "c" ("a" :: "b" :: "c" :: "d" :: "e" :: [])).
    { simpl. right. right. left. reflexivity. }
    pose proof (Hrl Hin_right) as Hin_left.
    simpl in Hin_left.
    destruct Hin_left as [Ha|Hin_left].
    + discriminate Ha.
    + destruct Hin_left as [Hb|Hin_left].
      * discriminate Hb.
      * destruct Hin_left as [Hd|Hin_left].
        { discriminate Hd. }
        destruct Hin_left as [He|Hin_left].
        { discriminate He. }
        inversion Hin_left.
Qed.