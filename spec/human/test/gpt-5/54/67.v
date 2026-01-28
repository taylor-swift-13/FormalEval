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
  problem_54_spec "abcdcbadcbade" "aabcdefgb" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. inversion H.
  - intros Hprop.
    exfalso.
    destruct (Hprop "f") as [Hlr Hrl].
    assert (HR : In "f" (list_ascii_of_string "aabcdefgb")).
    { simpl. right. right. right. right. right. right. left. reflexivity. }
    specialize (Hrl HR).
    simpl in Hrl.
    destruct Hrl as [H|Hrl]. { congruence. }
    destruct Hrl as [H|Hrl]. { congruence. }
    destruct Hrl as [H|Hrl]. { congruence. }
    destruct Hrl as [H|Hrl]. { congruence. }
    destruct Hrl as [H|Hrl]. { congruence. }
    destruct Hrl as [H|Hrl]. { congruence. }
    destruct Hrl as [H|Hrl]. { congruence. }
    destruct Hrl as [H|Hrl]. { congruence. }
    destruct Hrl as [H|Hrl]. { congruence. }
    destruct Hrl as [H|Hrl]. { congruence. }
    destruct Hrl as [H|Hrl]. { congruence. }
    destruct Hrl as [H|Hrl]. { congruence. }
    destruct Hrl as [H|Hrl]. { congruence. }
    inversion Hrl.
Qed.