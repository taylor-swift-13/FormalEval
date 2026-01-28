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

Lemma problem_29_example : problem_29_spec ["world"; "house"] "h" ["house"].
Proof.
  unfold problem_29_spec.
  split.
  - (* Prove is_subsequence ["house"] ["world"; "house"] *)
    apply sub_cons_skip.
    apply sub_cons_match.
    apply sub_nil.
  - (* Prove the logical equivalence for membership *)
    intros s.
    split.
    + (* Direction: In s ["house"] -> ... *)
      intros H_in.
      simpl in H_in.
      destruct H_in as [H_eq | H_false].
      * (* Case: s = "house" *)
        subst s.
        split.
        -- (* In "house" ["world"; "house"] *)
           simpl. right. left. reflexivity.
        -- (* prefix "h" "house" = true *)
           reflexivity.
      * (* Case: False *)
        contradiction.
    + (* Direction: (In s input /\ prefix "h" s = true) -> In s ["house"] *)
      intros [H_in H_prefix].
      simpl in H_in.
      destruct H_in as [H_world | [H_house | H_false]].
      * (* Case: s = "world" *)
        subst s.
        (* prefix "h" "world" evaluates to false *)
        simpl in H_prefix.
        discriminate H_prefix.
      * (* Case: s = "house" *)
        subst s.
        simpl. left. reflexivity.
      * (* Case: False *)
        contradiction.
Qed.