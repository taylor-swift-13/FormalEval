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
  problem_54_spec "llohelldefo" "llo" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. apply False_ind. discriminate H.
  - intros Hprop. apply False_ind.
    pose proof (Hprop "h") as Heq.
    assert (Hin0 : In "h" ["l"; "l"; "o"; "h"; "e"; "l"; "l"; "d"; "e"; "f"; "o"]).
    { right. right. right. left. reflexivity. }
    apply Heq in Hin0.
    simpl in Hin0.
    destruct Hin0 as [H|Hin0].
    + inversion H.
    + destruct Hin0 as [H|Hin0].
      * inversion H.
      * destruct Hin0 as [H|Hin0].
        { inversion H. }
        { inversion Hin0. }
Qed.