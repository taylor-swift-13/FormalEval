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
  problem_54_spec "5432caaaabacaabcd" "cabcd" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. exfalso. discriminate H.
  - intros H. exfalso.
    pose proof (H "5"%char) as H5.
    destruct H5 as [H51 H52].
    assert (In "5"%char (list_ascii_of_string "5432caaaabacaabcd")) as Hin0.
    { simpl. left. reflexivity. }
    specialize (H51 Hin0).
    simpl in H51.
    destruct H51 as [Hc|H51]; [inversion Hc|].
    destruct H51 as [Ha|H51]; [inversion Ha|].
    destruct H51 as [Hb|H51]; [inversion Hb|].
    destruct H51 as [Hc2|H51]; [inversion Hc2|].
    destruct H51 as [Hd|H51]; [inversion Hd|].
    inversion H51.
Qed.