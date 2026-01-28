Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

(*  Filter an input list of strings only for ones that start with a given prefix. *)

(*
  子列表定义
*)
Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : forall l, is_subsequence [] l
  | sub_cons_match : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_skip : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).


(* Pre: no additional constraints for `filter_by_prefix` by default *)
Definition problem_29_pre (input : list string) : Prop := True.

Definition problem_29_spec (input : list string) (substring : string) (output : list string) : Prop :=
  (* 1. output is a subsequence of input *)
  is_subsequence output input /\

  (* 2. A string is in output iff it is in input and starts with the prefix *)
  (forall s, In s output <-> (In s input /\ String.prefix substring s = true)).

Lemma problem_29_example : problem_29_spec ["xxx"; "asd"; "xxy"; "john doe"; "xxxAAA"; "xxx"] "xxx" ["xxx"; "xxxAAA"; "xxx"].
Proof.
  unfold problem_29_spec.
  split.
  - apply sub_cons_match.
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_nil.
  - intros s.
    split.
    + intros H.
      simpl in H.
      destruct H as [H | [H | [H | H]]]; subst.
      * split; [simpl; auto | reflexivity].
      * split; [simpl; auto 10 | reflexivity].
      * split; [simpl; auto | reflexivity].
      * contradiction.
    + intros [H_in H_pre].
      simpl in H_in.
      destruct H_in as [H | [H | [H | [H | [H | [H | H]]]]]]; subst.
      * simpl. left. reflexivity.
      * simpl in H_pre. discriminate.
      * simpl in H_pre. discriminate.
      * simpl in H_pre. discriminate.
      * simpl. right. left. reflexivity.
      * simpl. right. right. left. reflexivity.
      * contradiction.
Qed.