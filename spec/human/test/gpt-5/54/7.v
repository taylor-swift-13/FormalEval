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
  problem_54_spec "aabb" "aaccc" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. exfalso. discriminate H.
  - intros H.
    exfalso.
    specialize (H "b") as Hb.
    destruct Hb as [Hlr Hrl].
    assert (Hin_left_b : In "b" ("a" :: "a" :: "b" :: "b" :: [])).
    { simpl. right. right. left. reflexivity. }
    pose proof (Hlr Hin_left_b) as Hin_right_b.
    simpl in Hin_right_b.
    destruct Hin_right_b as [H1|Hrest].
    { discriminate H1. }
    destruct Hrest as [H2|Hrest].
    { discriminate H2. }
    destruct Hrest as [H3|Hrest].
    { discriminate H3. }
    destruct Hrest as [H4|Hrest].
    { discriminate H4. }
    destruct Hrest as [H5|Hrest].
    { discriminate H5. }
    inversion Hrest.
Qed.