Require Import List Ascii String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no special constraints for `same_chars` *)
Definition problem_54_pre (s0 s1 : string) : Prop := True.

Definition problem_54_spec (s0 s1 : string) (b : bool) : Prop :=
  let list_s0 := list_ascii_of_string s0 in
  let list_s1 := list_ascii_of_string s1 in
  b = true <-> (forall (c : ascii), In c list_s0 <-> In c list_s1).

Example test_problem_54 : problem_54_spec "abc" "def" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. discriminate.
  - intros H.
    specialize (H "a"%char).
    destruct H as [H1 _].
    assert (HIn: In "a"%char (list_ascii_of_string "abc")).
    { simpl. left. reflexivity. }
    apply H1 in HIn.
    simpl in HIn.
    repeat (destruct HIn as [HIn | HIn]; [ inversion HIn | ]).
    destruct HIn.
Qed.