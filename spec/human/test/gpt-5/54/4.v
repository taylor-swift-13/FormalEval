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
  problem_54_spec "eabcd" "dddddddabc" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. exfalso. discriminate H.
  - intros H.
    pose proof (H "e") as He.
    destruct He as [He12 He21].
    assert (Hin : In "e" (list_ascii_of_string "dddddddabc")).
    { apply He12. simpl. left. reflexivity. }
    simpl in Hin.
    destruct Hin as [H1|Hin]. { discriminate H1. }
    destruct Hin as [H1|Hin]. { discriminate H1. }
    destruct Hin as [H1|Hin]. { discriminate H1. }
    destruct Hin as [H1|Hin]. { discriminate H1. }
    destruct Hin as [H1|Hin]. { discriminate H1. }
    destruct Hin as [H1|Hin]. { discriminate H1. }
    destruct Hin as [H1|Hin]. { discriminate H1. }
    destruct Hin as [H1|Hin]. { discriminate H1. }
    destruct Hin as [H1|Hin]. { discriminate H1. }
    destruct Hin as [H1|Hin]. { discriminate H1. }
    inversion Hin.
Qed.