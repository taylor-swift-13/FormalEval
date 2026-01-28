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

Lemma starts_properly : forall l, is_correctly_bracketed l -> l = [] \/ exists l', l = "("%char :: l'.
Proof.
  intros l H. induction H.
  - left. reflexivity.
  - right. exists (l ++ [")"%char]). reflexivity.
  - destruct IHis_correctly_bracketed1 as [H1 | [l1' H1]].
    + subst. simpl. assumption.
    + subst. right. exists (l1' ++ l2). reflexivity.
Qed.

Example test_case_1 : problem_61_spec (list_ascii_of_string ")()()))()()()())(()((((())((())))())))") false.
Proof.
  unfold problem_61_spec.
  split.
  - intros H. discriminate.
  - intros H.
    apply starts_properly in H.
    destruct H as [H | [l' H]].
    + simpl in H. discriminate.
    + simpl in H. discriminate.
Qed.