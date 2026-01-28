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
  problem_54_spec "524321" "5432" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H.
    inversion H.
  - intros H.
    exfalso.
    specialize (H "1"%char).
    destruct H as [Hlr Hrl].
    assert (Hin_left : In "1"%char ("5"%char :: "2"%char :: "4"%char :: "3"%char :: "2"%char :: "1"%char :: nil)).
    { simpl. right. right. right. right. right. left. reflexivity. }
    specialize (Hlr Hin_left).
    simpl in Hlr.
    destruct Hlr as [H5|Hlr]; [discriminate H5|].
    destruct Hlr as [H4|Hlr]; [discriminate H4|].
    destruct Hlr as [H3|Hlr]; [discriminate H3|].
    destruct Hlr as [H2|Hlr]; [discriminate H2|].
    inversion Hlr.
Qed.