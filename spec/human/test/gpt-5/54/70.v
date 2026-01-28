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
  problem_54_spec "abcdegfedcba" "5432" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. congruence.
  - intros H.
    specialize (H "a"%char).
    destruct H as [H1 H2].
    assert (Hin_s0 : In "a"%char ("a"%char :: "b"%char :: "c"%char :: "d"%char :: "e"%char :: "g"%char :: "f"%char :: "e"%char :: "d"%char :: "c"%char :: "b"%char :: "a"%char :: [])).
    { simpl. left. reflexivity. }
    specialize (H1 Hin_s0).
    simpl in H1.
    destruct H1 as [H1|H1].
    + congruence.
    + destruct H1 as [H1|H1].
      * congruence.
      * destruct H1 as [H1|H1].
        { congruence. }
        destruct H1 as [H1|H1].
        { congruence. }
        inversion H1.
Qed.