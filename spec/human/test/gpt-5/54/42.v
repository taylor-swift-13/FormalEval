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
  problem_54_spec "5432caaaabacaababbcccddddeeeeecd" "abcd" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. exfalso. discriminate H.
  - intros H.
    exfalso.
    specialize (H "5"%char).
    destruct H as [HL HR].
    assert (Hin0 : In "5"%char (list_ascii_of_string "5432caaaabacaababbcccddddeeeeecd")).
    { simpl. left. reflexivity. }
    specialize (HL Hin0) as Hin1.
    simpl in Hin1.
    destruct Hin1 as [E|Hin1]; [congruence|].
    destruct Hin1 as [E|Hin1]; [congruence|].
    destruct Hin1 as [E|Hin1]; [congruence|].
    destruct Hin1 as [E|Hin1]; [congruence|].
    inversion Hin1.
Qed.