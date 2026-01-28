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
  problem_54_spec "5432caaaabacaabcd" "abcd" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. exfalso. discriminate H.
  - intros H.
    exfalso.
    specialize (H "5").
    simpl in H.
    destruct H as [H1 H2].
    assert (In "5" ("5" :: "4" :: "3" :: "2" :: "c" :: "a" :: "a" :: "a" :: "a" :: "b" :: "a" :: "c" :: "a" :: "a" :: "b" :: "c" :: "d" :: [])) as Hin0.
    { simpl. left. reflexivity. }
    pose proof (H1 Hin0) as Hin1.
    simpl in Hin1.
    destruct Hin1 as [Ha|Hin1]; [discriminate Ha|].
    destruct Hin1 as [Hb|Hin1]; [discriminate Hb|].
    destruct Hin1 as [Hc|Hin1]; [discriminate Hc|].
    destruct Hin1 as [Hd|Hin1]; [discriminate Hd|].
    inversion Hin1.
Qed.