Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

(*  Filter an input list of strings only for ones that start with a given prefix. *)

Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : forall l, is_subsequence [] l
  | sub_cons_match : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_skip : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).

Definition problem_29_pre (input : list string) : Prop := True.

Definition problem_29_spec (input : list string) (substring : string) (output : list string) : Prop :=
  is_subsequence output input /\
  (forall s, In s output <-> (In s input /\ String.prefix substring s = true)).

Lemma problem_29_example : problem_29_spec ["java" ; "java"] "x" [].
Proof.
  unfold problem_29_spec.
  split.
  - apply sub_nil.
  - intros s.
    split.
    + intros H_in_nil.
      inversion H_in_nil.
    + intros [H_in H_prefix].
      simpl in H_in.
      destruct H_in as [H_java1 | [H_java2 | H_false]].
      * subst s.
        simpl in H_prefix.
        discriminate H_prefix.
      * subst s.
        simpl in H_prefix.
        discriminate H_prefix.
      * contradiction.
Qed.