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
  problem_54_spec "cdcd" "" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. inversion H.
  - intros Hall.
    exfalso.
    pose (ch := "c"%char).
    specialize (Hall ch).
    destruct Hall as [H1 H2].
    assert (Hin : In ch ["c"%char; "d"%char; "c"%char; "d"%char]).
    { simpl. left. reflexivity. }
    apply H1 in Hin.
    inversion Hin.
Qed.