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
  problem_54_spec "543543221" "abcdeadbbcccddddeeeeehelldefogfedcba" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    specialize (H "a"%char).
    destruct H as [Hlr Hrl].
    assert (Hin1 : In "a"%char (list_ascii_of_string "abcdeadbbcccddddeeeeehelldefogfedcba")).
    { simpl. left. reflexivity. }
    specialize (Hrl Hin1).
    simpl in Hrl.
    destruct Hrl as [Hhd|Hrl]; [discriminate|].
    destruct Hrl as [Hhd|Hrl]; [discriminate|].
    destruct Hrl as [Hhd|Hrl]; [discriminate|].
    destruct Hrl as [Hhd|Hrl]; [discriminate|].
    destruct Hrl as [Hhd|Hrl]; [discriminate|].
    destruct Hrl as [Hhd|Hrl]; [discriminate|].
    destruct Hrl as [Hhd|Hrl]; [discriminate|].
    destruct Hrl as [Hhd|Hrl]; [discriminate|].
    destruct Hrl as [Hhd|Hrl]; [discriminate|].
    inversion Hrl.
Qed.