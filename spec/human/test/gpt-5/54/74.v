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
  problem_54_spec "llaaa1234a5bbbccco" "llo" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H.
    exfalso.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H "a") as Ha.
    simpl in Ha.
    assert (Hin_left: In "a" (list_ascii_of_string "llaaa1234a5bbbccco")).
    { simpl. right. right. left. reflexivity. }
    apply Ha in Hin_left.
    simpl in Hin_left.
    destruct Hin_left as [H1|Hrest1].
    { discriminate H1. }
    simpl in Hrest1.
    destruct Hrest1 as [H2|Hrest2].
    { discriminate H2. }
    simpl in Hrest2.
    destruct Hrest2 as [H3|Hnil].
    { discriminate H3. }
    inversion Hnil.
Qed.