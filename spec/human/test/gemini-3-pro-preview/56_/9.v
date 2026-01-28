Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

(* Inductive definition of correctly bracketed strings *)
Inductive is_correctly_bracketed : string -> Prop :=
  | cb_nil    : is_correctly_bracketed ""
  | cb_nest   : forall l,
                  is_correctly_bracketed l ->
                  is_correctly_bracketed ("<" ++ l ++ ">")
  | cb_concat : forall l1 l2,
                  is_correctly_bracketed l1 ->
                  is_correctly_bracketed l2 ->
                  is_correctly_bracketed (l1 ++ l2).

(* Precondition definition *)
Definition problem_56_pre (brackets : string) : Prop :=
    Forall (fun c => c = "<"%char \/ c = ">"%char) (list_ascii_of_string brackets).

(* Specification definition *)
Definition problem_56_spec (brackets : string) (b : bool) : Prop :=
  b = true <-> is_correctly_bracketed brackets.

Example test_correct_bracketing_fail : problem_56_spec ">" false.
Proof.
  unfold problem_56_spec.
  split.
  - intros H. discriminate.
  - intros H.
    assert (Hstart: forall s, is_correctly_bracketed s -> s = "" \/ exists s', s = String "<"%char s').
    {
      intros s Hcb. induction Hcb.
      - left. reflexivity.
      - right. exists (l ++ ">"). reflexivity.
      - destruct IHHcb1 as [Hl1 | [s' Hl1]].
        + subst l1. simpl. apply IHHcb2.
        + right. subst l1. simpl. exists (s' ++ l2). reflexivity.
    }
    apply Hstart in H.
    destruct H as [H | [s' H]].
    + discriminate.
    + inversion H.
Qed.