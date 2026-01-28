Require Import List Ascii String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no special constraints for `same_chars` *)
Definition problem_54_pre (s0 s1 : string) : Prop := True.

Definition problem_54_spec (s0 s1 : string) (b : bool) : Prop :=
  let list_s0 := list_ascii_of_string s0 in
  let list_s1 := list_ascii_of_string s1 in
  b = true <-> (forall (c : ascii), In c list_s0 <-> In c list_s1).

Example test_problem_54 : problem_54_spec "5432cababecdead" "cababecdead" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. discriminate.
  - intros H.
    specialize (H "5"%char).
    assert (H_in : In "5"%char (list_ascii_of_string "5432cababecdead")).
    { simpl. left. reflexivity. }
    apply H in H_in.
    simpl in H_in.
    repeat (destruct H_in as [C | H_in]; [ inversion C | ]).
    destruct H_in.
Qed.