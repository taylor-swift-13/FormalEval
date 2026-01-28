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

Lemma cb_head :
  forall s, is_correctly_bracketed s -> s = "" \/ exists t, s = String "<"%char t.
Proof.
  intros s H. induction H.
  - left. reflexivity.
  - right. exists (l ++ ">"). simpl. reflexivity.
  - destruct IHis_correctly_bracketed1 as [Hl1 | [t1 Hl1]].
    + rewrite Hl1. simpl. exact IHis_correctly_bracketed2.
    + right. exists (t1 ++ l2). rewrite Hl1. simpl. reflexivity.
Qed.

Example problem_56_test_case_1 :
  problem_56_spec ">><<" false.
Proof.
  unfold problem_56_spec.
  split.
  - intros H. discriminate H.
  - intros Hcb.
    destruct (cb_head ">><<" Hcb) as [Hemp | [t Hstart]].
    + discriminate Hemp.
    + discriminate Hstart.
Qed.