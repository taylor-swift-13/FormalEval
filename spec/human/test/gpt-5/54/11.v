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
  problem_54_spec "abc" "def" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H.
    exfalso.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H "a"%char).
    destruct H as [Hl Hr].
    assert (Hin : In "a"%char ["a"%char; "b"%char; "c"%char]).
    { simpl. left. reflexivity. }
    specialize (Hl Hin).
    simpl in Hl.
    destruct Hl as [H1 | Hl].
    + discriminate H1.
    + destruct Hl as [H2 | Hl].
      * discriminate H2.
      * destruct Hl as [H3 | H4].
        { discriminate H3. }
        { exact H4. }
Qed.