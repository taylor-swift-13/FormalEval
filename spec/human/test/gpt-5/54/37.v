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
  problem_54_spec "5432" "cdcd5432" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (~ In "c"%char ["5"%char; "4"%char; "3"%char; "2"%char]) as Hnot.
    { intros HIn.
      simpl in HIn.
      destruct HIn as [E|HIn]; [ inversion E | ].
      destruct HIn as [E|HIn]; [ inversion E | ].
      destruct HIn as [E|HIn]; [ inversion E | ].
      destruct HIn as [E|HIn]; [ inversion E | inversion HIn ].
    }
    apply Hnot.
    apply (proj2 (H "c"%char)).
    simpl. left. reflexivity.
Qed.