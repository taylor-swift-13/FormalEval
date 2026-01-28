Require Import List Ascii String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no special constraints for `same_chars` *)
Definition problem_54_pre (s0 s1 : string) : Prop := True.

Definition problem_54_spec (s0 s1 : string) (b : bool) : Prop :=
  let list_s0 := list_ascii_of_string s0 in
  let list_s1 := list_ascii_of_string s1 in
  b = true <-> (forall (c : ascii), In c list_s0 <-> In c list_s1).

Example test_problem_54 : problem_54_spec "llo" "helleo" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. inversion H.
  - intros H.
    specialize (H "h"%char).
    destruct H as [_ H].
    assert (Hin : In "h"%char (list_ascii_of_string "helleo")).
    { simpl. left. reflexivity. }
    apply H in Hin.
    simpl in Hin.
    repeat (destruct Hin as [C | Hin]; [ discriminate | ]).
    destruct Hin.
Qed.