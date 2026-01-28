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


Definition problem_56_pre (brackets : string) : Prop :=
    Forall (fun c => c = "<"%char \/ c = ">"%char) (list_ascii_of_string brackets).

Definition problem_56_spec (brackets : string) (b : bool) : Prop :=
  b = true <-> is_correctly_bracketed brackets.

Lemma cb_empty_or_starts_with_lt :
  forall s, is_correctly_bracketed s ->
    s = "" \/ exists r, s = "<" ++ r.
Proof.
  intros s H.
  induction H as [| l H IH | l1 l2 H1 IH1 H2 IH2].
  - left. reflexivity.
  - right. exists (l ++ ">"). reflexivity.
  - destruct IH1 as [He1 | [r1 Hr1]].
    + rewrite He1. simpl. exact IH2.
    + right. exists (r1 ++ l2). rewrite Hr1. simpl. reflexivity.
Qed.

Example problem_56_test_case_1 :
  problem_56_spec "><" false.
Proof.
  unfold problem_56_spec.
  split.
  - intros H. discriminate H.
  - intros Hcb.
    exfalso.
    destruct (cb_empty_or_starts_with_lt "><" Hcb) as [He | [r Hr]].
    + discriminate He.
    + simpl in Hr. injection Hr as Hc _. inversion Hc.
Qed.