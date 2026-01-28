(* def correct_bracketing(brackets: str):
 brackets is a string of "<" and ">".
return True if every opening bracket has a corresponding closing bracket.

>>> correct_bracketing("<")
False
>>> correct_bracketing("<>")
True
>>> correct_bracketing("<<><>>")
True
>>> correct_bracketing("><<>")
False
*)
(* 引入Coq标准库，用于列表（List）和ASCII字符（Ascii）的定义 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Open Scope string_scope.


Inductive is_correctly_bracketed : string -> Prop :=
  | cb_nil    : is_correctly_bracketed ""
  | cb_nest   : forall l,
                  is_correctly_bracketed l ->
                  is_correctly_bracketed ("<" ++ l ++ ">")
  | cb_concat : forall l1 l2,
                  is_correctly_bracketed l1 ->
                  is_correctly_bracketed l2 ->
                  is_correctly_bracketed (l1 ++ l2).


(* Pre: no special constraints for `correct_bracketing` *)
Definition problem_56_pre (brackets : string) : Prop :=
    Forall (fun c => c = "<"%char \/ c = ">"%char) (list_ascii_of_string brackets).

Definition problem_56_spec (brackets : string) (b : bool) : Prop :=
  b = true <-> is_correctly_bracketed brackets.

Example problem_56_test_case_1 :
  problem_56_spec "><<<><<><><><>>>><><>>" false.
Proof.
  unfold problem_56_spec.
  split.
  - intros H. discriminate H.
  - intros Hcb.
    assert (Hstart: forall s : string, is_correctly_bracketed s -> s = "" \/ exists s', s = String "<"%char s').
    { intros s0 H0.
      induction H0.
      - left. reflexivity.
      - right. exists (l ++ ">"). simpl. reflexivity.
      - destruct IHis_correctly_bracketed1 as [Hempty1 | [s1 Hr1]].
        + rewrite Hempty1. apply IHis_correctly_bracketed2.
        + rewrite Hr1. right. exists (s1 ++ l2). simpl. reflexivity.
    }
    destruct (Hstart "><<<><<><><><>>>><><>>" Hcb) as [Hempty | [r Hr]].
    + discriminate Hempty.
    + discriminate Hr.
Qed.