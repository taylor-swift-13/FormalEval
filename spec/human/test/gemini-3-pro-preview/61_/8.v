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

Lemma cb_not_only_open : forall l, is_correctly_bracketed l -> 
  Forall (fun c => c = "("%char) l -> l = [].
Proof.
  intros l Hcb Hall.
  induction Hcb.
  - reflexivity.
  - rewrite Forall_forall in Hall.
    assert (In ")"%char ("("%char :: l ++ [")"%char])).
    { simpl. right. apply in_or_app. right. left. reflexivity. }
    apply Hall in H. discriminate H.
  - apply Forall_app in Hall. destruct Hall as [H1 H2].
    apply IHHcb1 in H1. apply IHHcb2 in H2.
    subst. reflexivity.
Qed.

Example test_case_1 : problem_61_spec ["("%char; "("%char; "("%char; "("%char] false.
Proof.
  unfold problem_61_spec.
  split; intros H.
  - discriminate H.
  - apply cb_not_only_open in H.
    + discriminate H.
    + repeat constructor; reflexivity.
Qed.