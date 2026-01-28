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
  problem_54_spec "abcd" "dddddddabcf" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H.
    inversion H.
  - intros H.
    simpl in H.
    specialize (H "f").
    destruct H as [Hlf_rf Hrf_lf].
    assert (Hin_right : In "f" (list_ascii_of_string "dddddddabcf")).
    { simpl.
      right. right. right. right. right. right. right. right. right. right.
      left. reflexivity. }
    specialize (Hrf_lf Hin_right).
    exfalso.
    simpl in Hrf_lf.
    destruct Hrf_lf as [Ha|Hrest].
    + inversion Ha.
    + destruct Hrest as [Hb|Hrest].
      * inversion Hb.
      * destruct Hrest as [Hc|Hrest].
        { inversion Hc. }
        destruct Hrest as [Hd|Hnil].
        { inversion Hd. }
        inversion Hnil.
Qed.