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

Lemma problem_29_example : problem_29_spec ["apple"; "banana"; "orange"; "apricot"; "kiwi"] "ap" ["apple"; "apricot"].
Proof.
  unfold problem_29_spec.
  split.
  - (* Prove is_subsequence *)
    apply sub_cons_match.
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_match.
    apply sub_cons_skip.
    apply sub_nil.
  - (* Prove the logical equivalence for membership *)
    intros s.
    split.
    + (* Direction: In s output -> ... *)
      intros H_in.
      simpl in H_in.
      destruct H_in as [H_apple | [H_apricot | H_false]].
      * (* Case: s = "apple" *)
        subst s.
        split.
        -- simpl. left. reflexivity.
        -- reflexivity.
      * (* Case: s = "apricot" *)
        subst s.
        split.
        -- simpl. right. right. right. left. reflexivity.
        -- reflexivity.
      * (* Case: False *)
        contradiction.
    + (* Direction: (In s input /\ prefix "ap" s = true) -> In s output *)
      intros [H_in H_prefix].
      simpl in H_in.
      destruct H_in as [H_apple | [H_banana | [H_orange | [H_apricot | [H_kiwi | H_false]]]]].
      * (* Case: s = "apple" *)
        subst s.
        simpl. left. reflexivity.
      * (* Case: s = "banana" *)
        subst s.
        simpl in H_prefix. discriminate H_prefix.
      * (* Case: s = "orange" *)
        subst s.
        simpl in H_prefix. discriminate H_prefix.
      * (* Case: s = "apricot" *)
        subst s.
        simpl. right. left. reflexivity.
      * (* Case: s = "kiwi" *)
        subst s.
        simpl in H_prefix. discriminate H_prefix.
      * (* Case: False *)
        contradiction.
Qed.