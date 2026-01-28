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
  problem_54_spec "aaabbbccc" "world" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H.
    exfalso.
    discriminate H.
  - intros H.
    exfalso.
    pose proof (proj1 (H "a")) as Hdir.
    assert (Hin0 : In "a" (list_ascii_of_string "aaabbbccc")).
    { simpl. left. reflexivity. }
    pose proof (Hdir Hin0) as Hin1.
    simpl in Hin1.
    destruct Hin1 as [H1|Hin1].
    + discriminate H1.
    + destruct Hin1 as [H2|Hin1].
      * discriminate H2.
      * destruct Hin1 as [H3|Hin1].
        { discriminate H3. }
        destruct Hin1 as [H4|Hin1].
        { discriminate H4. }
        destruct Hin1 as [H5|Hin1].
        { discriminate H5. }
        inversion Hin1.
Qed.