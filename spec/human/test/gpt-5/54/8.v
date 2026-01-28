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
  problem_54_spec "ab" "cd" false.
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
    destruct H as [Hlr _].
    assert (Hin_left : In "a"%char ["a"%char; "b"%char]).
    { simpl. left. reflexivity. }
    pose proof (Hlr Hin_left) as Hin_right.
    simpl in Hin_right.
    destruct Hin_right as [Hac|[Had|Hnil]]; try congruence; inversion Hnil.
Qed.