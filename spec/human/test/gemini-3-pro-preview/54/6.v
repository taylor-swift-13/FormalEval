Require Import List Ascii String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no special constraints for `same_chars` *)
Definition problem_54_pre (s0 s1 : string) : Prop := True.

Definition problem_54_spec (s0 s1 : string) (b : bool) : Prop :=
  let list_s0 := list_ascii_of_string s0 in
  let list_s1 := list_ascii_of_string s1 in
  b = true <-> (forall (c : ascii), In c list_s0 <-> In c list_s1).

Example test_problem_54 : problem_54_spec "eabcdzzzz" "dddzzzzzzzddddabc" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. discriminate.
  - intros H.
    specialize (H "e"%char).
    destruct H as [H1 _].
    assert (Hin : In "e"%char (list_ascii_of_string "eabcdzzzz")).
    { simpl. left. reflexivity. }
    apply H1 in Hin.
    simpl in Hin.
    repeat (destruct Hin as [C | Hin]; [ discriminate C | ]).
    destruct Hin.
Qed.