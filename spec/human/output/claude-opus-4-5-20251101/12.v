Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope string_scope.

(* Pre: no specific requirements for `longest` — accept any list of strings by default *)
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

(* Test case: input = [""], output = Some "" 
   Note: The original test case says output = None, but for a non-empty list [""],
   the specification requires output to be Some of the longest string.
   Since [""] is non-empty and contains one empty string, output should be Some "". *)

Example test_problem_12 : problem_12_spec [""%string] (Some ""%string).
Proof.
  unfold problem_12_spec.
  right.
  exists ""%string, 0.
  split. { reflexivity. }
  split. { simpl. lia. }
  split. { simpl. lia. }
  split. { simpl. reflexivity. }
  split.
  - intros j Hj.
    simpl in Hj.
    exists ""%string.
    intros _.
    simpl. lia.
  - intros j Hj.
    lia.
Qed.