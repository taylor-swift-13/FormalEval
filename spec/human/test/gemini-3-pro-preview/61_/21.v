Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii Coq.Strings.String.
Import ListNotations.

Inductive is_correctly_bracketed : list ascii -> Prop :=
  | cb_nil    : is_correctly_bracketed []
  | cb_nest   : forall l,
                  is_correctly_bracketed l ->
                  is_correctly_bracketed ("("%char :: l ++ [")"%char])
  | cb_concat : forall l1 l2,
                  is_correctly_bracketed l1 ->
                  is_correctly_bracketed l2 ->
                  is_correctly_bracketed (l1 ++ l2).

Definition problem_61_pre (brackets : string) : Prop :=
  Forall (fun c => c = "("%char \/ c = ")"%char) (list_ascii_of_string brackets).

Definition problem_61_spec (brackets : list ascii) (b : bool) : Prop :=
  b = true <-> is_correctly_bracketed brackets.

Example test_case_1 : problem_61_spec [")"%char; "("%char] false.
Proof.
  unfold problem_61_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    assert (H_prop : forall l, is_correctly_bracketed l -> l = [] \/ exists tl, l = "("%char :: tl).
    {
      clear H. intros l H_cb. induction H_cb.
      - left. reflexivity.
      - right. exists (l ++ [")"%char]). reflexivity.
      - destruct IHH_cb1 as [H_nil | [tl H_cons]].
        + subst. simpl. apply IHH_cb2.
        + subst. simpl. right. exists (tl ++ l2). reflexivity.
    }
    apply H_prop in H.
    destruct H as [H_nil | [tl H_cons]].
    + discriminate H_nil.
    + injection H_cons as H_eq. discriminate H_eq.
Qed.