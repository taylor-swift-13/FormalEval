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

(* 
   Test case: input = ["world"; "heworldlo"; "house"], substring = "h", output = ["heworldlo"; "house"]
*)
Lemma problem_29_example : problem_29_spec ["world"; "heworldlo"; "house"] "h" ["heworldlo"; "house"].
Proof.
  unfold problem_29_spec.
  split.
  - (* Prove is_subsequence *)
    apply sub_cons_skip.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_nil.
  - (* Prove the logical equivalence for membership *)
    intros s.
    split.
    + (* Direction: In s output -> (In s input /\ prefix "h" s = true) *)
      intros H_in_out.
      simpl in H_in_out.
      destruct H_in_out as [H_hew | [H_hou | H_false]].
      * (* s = "heworldlo" *)
        subst.
        split.
        -- simpl. right. left. reflexivity.
        -- reflexivity.
      * (* s = "house" *)
        subst.
        split.
        -- simpl. right. right. left. reflexivity.
        -- reflexivity.
      * contradiction.
    + (* Direction: (In s input /\ prefix "h" s = true) -> In s output *)
      intros [H_in_inp H_pref].
      simpl in H_in_inp.
      destruct H_in_inp as [H_world | [H_hew | [H_hou | H_false]]].
      * (* s = "world" *)
        subst.
        simpl in H_pref.
        discriminate H_pref.
      * (* s = "heworldlo" *)
        subst.
        simpl. left. reflexivity.
      * (* s = "house" *)
        subst.
        simpl. right. left. reflexivity.
      * contradiction.
Qed.