Require Import List Ascii String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no special constraints for `same_chars` *)
Definition problem_54_pre (s0 s1 : string) : Prop := True.

Definition problem_54_spec (s0 s1 : string) (b : bool) : Prop :=
  let list_s0 := list_ascii_of_string s0 in
  let list_s1 := list_ascii_of_string s1 in
  b = true <-> (forall (c : ascii), In c list_s0 <-> In c list_s1).

Example test_problem_54 : problem_54_spec "dddddddabc" "abcd" true.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros _.
    intros c.
    split; intros H.
    + repeat (destruct H as [H | H]; [ 
        subst; simpl; tauto 
      | ]).
      destruct H.
    + repeat (destruct H as [H | H]; [ 
        subst; simpl; tauto 
      | ]).
      destruct H.
  - intros _.
    reflexivity.
Qed.