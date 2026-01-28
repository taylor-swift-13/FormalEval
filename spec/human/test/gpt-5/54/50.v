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
  problem_54_spec "cdcd" "ccd5143241cd" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. inversion H.
  - intros H.
    exfalso.
    specialize (H "1"%char).
    destruct H as [Hto Hfrom].
    assert (Hin_s1 : In "1"%char (list_ascii_of_string "ccd5143241cd")).
    { simpl. right. right. right. right. left. reflexivity. }
    pose proof (Hfrom Hin_s1) as Hin_s0.
    simpl in Hin_s0.
    destruct Hin_s0 as [Hc|Hrest1].
    + inversion Hc.
    + destruct Hrest1 as [Hd|Hrest2].
      * inversion Hd.
      * destruct Hrest2 as [Hc2|Hrest3].
        { inversion Hc2. }
        { destruct Hrest3 as [Hd2|Hnil].
          - inversion Hd2.
          - inversion Hnil. }
Qed.