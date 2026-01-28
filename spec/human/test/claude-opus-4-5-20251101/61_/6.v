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

Lemma not_bracketed_close_first : forall l,
  is_correctly_bracketed (")"%char :: l) -> False.
Proof.
  intros l H.
  remember (")"%char :: l) as s eqn:Heq.
  revert l Heq.
  induction H; intros.
  - discriminate.
  - injection Heq. intros Heq1 Heq2.
    inversion Heq2.
  - destruct l1.
    + simpl in Heq. apply IHis_correctly_bracketed2 with (l := l). exact Heq.
    + simpl in Heq. injection Heq. intros Heq1 Heq2.
      subst a.
      apply IHis_correctly_bracketed1 with (l := l1). reflexivity.
Qed.

Example test_problem_61 : problem_61_spec [")"%char; "("%char; "("%char; ")"%char] false.
Proof.
  unfold problem_61_spec.
  split.
  - intros H. discriminate.
  - intros H. exfalso. apply not_bracketed_close_first with (l := ["("%char; "("%char; ")"%char]). exact H.
Qed.