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

Lemma problem_29_example : problem_29_spec ["a"; "ab"; "abc"; "ba"; "bb"; "bc"] "banana" [].
Proof.
  unfold problem_29_spec.
  split.
  - (* Prove is_subsequence [] input *)
    apply sub_nil.
  - (* Prove the logical equivalence for membership *)
    intros s.
    split.
    + (* Direction: In s [] -> ... *)
      intros H_in_nil.
      inversion H_in_nil.
    + (* Direction: (In s input /\ prefix "banana" s = true) -> In s [] *)
      intros [H_in H_prefix].
      simpl in H_in.
      (* Decompose the list membership *)
      destruct H_in as [H_a | [H_ab | [H_abc | [H_ba | [H_bb | [H_bc | H_false]]]]]].
      * (* s = "a" *)
        subst s.
        simpl in H_prefix.
        discriminate H_prefix.
      * (* s = "ab" *)
        subst s.
        simpl in H_prefix.
        discriminate H_prefix.
      * (* s = "abc" *)
        subst s.
        simpl in H_prefix.
        discriminate H_prefix.
      * (* s = "ba" *)
        subst s.
        simpl in H_prefix.
        discriminate H_prefix.
      * (* s = "bb" *)
        subst s.
        simpl in H_prefix.
        discriminate H_prefix.
      * (* s = "bc" *)
        subst s.
        simpl in H_prefix.
        discriminate H_prefix.
      * (* s in [] *)
        contradiction.
Qed.