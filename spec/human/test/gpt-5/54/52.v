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
  problem_54_spec "aabcdefgb" "12345" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    specialize (H "a"%char) as [Hlr Hrl].
    assert (HL : In "a"%char ("a" :: "a" :: "b" :: "c" :: "d" :: "e" :: "f" :: "g" :: "b" :: [])).
    { left. reflexivity. }
    specialize (Hlr HL) as HR.
    simpl in HR.
    destruct HR as [H1|HR]; [inversion H1|].
    destruct HR as [H2|HR]; [inversion H2|].
    destruct HR as [H3|HR]; [inversion H3|].
    destruct HR as [H4|HR]; [inversion H4|].
    destruct HR as [H5|HR]; [inversion H5|].
    inversion HR.
Qed.