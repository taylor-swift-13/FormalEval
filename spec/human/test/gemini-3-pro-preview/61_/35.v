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

Lemma cb_starts_with_open : forall l,
  is_correctly_bracketed l ->
  match l with
  | [] => True
  | c :: _ => c = "("%char
  end.
Proof.
  intros l H.
  induction H.
  - exact I.
  - simpl. reflexivity.
  - destruct l1.
    + simpl in *. assumption.
    + simpl in *. destruct IHis_correctly_bracketed1. subst. reflexivity.
Qed.

Example test_case_1 : problem_61_spec (list_ascii_of_string ")()()()()))()()()())(())()") false.
Proof.
  unfold problem_61_spec.
  split.
  - intros H. inversion H.
  - intros H.
    apply cb_starts_with_open in H.
    simpl in H.
    discriminate.
Qed.