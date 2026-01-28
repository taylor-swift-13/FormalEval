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
  problem_54_spec "5432caaaabacaababbcccddddeeeeecd" "cabcd" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. inversion H.
  - intros H.
    specialize (H "5"%char).
    destruct H as [Hlr Hrl].
    assert (Hin0 : In "5"%char (list_ascii_of_string "5432caaaabacaababbcccddddeeeeecd")).
    { simpl. left. reflexivity. }
    pose proof (Hlr Hin0) as Hin1.
    simpl in Hin1.
    destruct Hin1 as [Hc | Hin1]; [inversion Hc|].
    destruct Hin1 as [Ha | Hin1]; [inversion Ha|].
    destruct Hin1 as [Hb | Hin1]; [inversion Hb|].
    destruct Hin1 as [Hc2 | Hin1]; [inversion Hc2|].
    destruct Hin1 as [Hd | Hin1]; [inversion Hd|].
    inversion Hin1.
Qed.