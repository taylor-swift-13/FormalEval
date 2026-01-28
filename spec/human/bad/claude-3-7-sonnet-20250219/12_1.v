Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

(* Specification *)

Definition problem_12_pre (input : list string) : Prop := True.

Definition problem_12_spec (input : list string) (output : option string) : Prop :=
  (input = [] /\ output = None) \/
  (exists out i,
    output = Some out /\
    List.length input > 0 /\
    i < List.length input /\
    nth_error input i = Some out /\
    (forall j, j < List.length input -> exists s, nth_error input j = Some s -> String.length s <= String.length out) /\
    (forall j, j < i -> exists s, nth_error input j = Some s -> String.length s < String.length out)
  ).

(* Test case: input = [""] (a list with one empty string), output = Some "" *)
Example test_case_single_empty_string :
  problem_12_spec [""] (Some "").
Proof.
  unfold problem_12_spec.
  right.
  exists "".
  exists 0.
  repeat split.
  - reflexivity.
  - simpl. lia.
  - simpl. lia.
  - simpl. reflexivity.
  - intros j Hj.
    exists (nth j [""] "").
    intros Hnth.
    rewrite nth_error_nth in Hnth by lia.
    rewrite Hnth.
    simpl.
    destruct (Nat.eq_dec j 0).
    + subst. simpl. lia.
    + simpl. lia.
  - intros j Hj.
    exists (nth j [""] "").
    intros Hnth.
    rewrite nth_error_nth in Hnth by lia.
    rewrite Hnth.
    simpl.
    lia.
Qed.

(* Test case: input = [], output = None *)
Example test_case_empty_list :
  problem_12_spec [] None.
Proof.
  unfold problem_12_spec.
  left.
  reflexivity.
Qed.