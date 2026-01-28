Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Open Scope string_scope.

Inductive is_correctly_bracketed : string -> Prop :=
  | cb_nil    : is_correctly_bracketed ""
  | cb_nest   : forall l,
                  is_correctly_bracketed l ->
                  is_correctly_bracketed ("<" ++ l ++ ">")
  | cb_concat : forall l1 l2,
                  is_correctly_bracketed l1 ->
                  is_correctly_bracketed l2 ->
                  is_correctly_bracketed (l1 ++ l2).

Definition problem_56_pre (brackets : string) : Prop :=
    Forall (fun c => c = "<"%char \/ c = ">"%char) (list_ascii_of_string brackets).

Definition problem_56_spec (brackets : string) (b : bool) : Prop :=
  b = true <-> is_correctly_bracketed brackets.

Lemma string_length_append : forall s1 s2,
  String.length (s1 ++ s2) = String.length s1 + String.length s2.
Proof.
  induction s1; intros; simpl.
  - reflexivity.
  - rewrite IHs1. reflexivity.
Qed.

Lemma not_correctly_bracketed_single_open : ~ is_correctly_bracketed "<".
Proof.
  intro H.
  remember "<" as s eqn:Heq.
  induction H.
  - discriminate.
  - assert (Hlen: String.length "<" = 1) by reflexivity.
    rewrite Heq in Hlen.
    simpl in Hlen.
    rewrite string_length_append in Hlen.
    simpl in Hlen.
    rewrite string_length_append in Hlen.
    simpl in Hlen.
    omega.
  - assert (Hlen: String.length "<" = 1) by reflexivity.
    rewrite Heq in Hlen.
    rewrite string_length_append in Hlen.
    destruct l1; simpl in *.
    + apply IHis_correctly_bracketed2. assumption.
    + discriminate.
Qed.

Example test_problem_56 : problem_56_spec "<" false.
Proof.
  unfold problem_56_spec.
  split.
  - intros H. discriminate.
  - intros H. exfalso. apply not_correctly_bracketed_single_open. exact H.
Qed.