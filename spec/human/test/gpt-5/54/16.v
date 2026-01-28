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
  problem_54_spec "hello" "world" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. discriminate.
  - intros H.
    exfalso.
    specialize (H "h"%char).
    destruct H as [H1 H2].
    assert (Hin_hello : In "h"%char (list_ascii_of_string "hello")).
    { simpl. left. reflexivity. }
    specialize (H1 Hin_hello).
    simpl in H1.
    destruct H1 as [H|H].
    + discriminate H.
    + destruct H as [H|H].
      * discriminate H.
      * destruct H as [H|H].
        -- discriminate H.
        -- destruct H as [H|H].
           ++ discriminate H.
           ++ destruct H as [H|H].
              ** discriminate H.
              ** inversion H.
Qed.