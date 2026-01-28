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
  problem_54_spec "aabcdefgb" "aaa" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    destruct (H "b") as [HL HR].
    assert (Hin0 : In "b" (list_ascii_of_string "aabcdefgb")).
    { simpl. right. right. left. reflexivity. }
    specialize (HL Hin0).
    simpl in HL.
    destruct HL as [E|HL]; [discriminate E|].
    destruct HL as [E|HL]; [discriminate E|].
    destruct HL as [E|HL]; [discriminate E|].
    inversion HL.
Qed.