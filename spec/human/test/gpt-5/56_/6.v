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

Example problem_56_test_case_1 :
  problem_56_spec "><<>" false.
Proof.
  unfold problem_56_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros Hcb. exfalso.
    assert (forall s, is_correctly_bracketed s ->
             match s with
             | EmptyString => True
             | String a _ => a <> ">"%char
             end) as Hlemma.
    { intros s H.
      induction H as [| l Hl IHl | l1 l2 H1 IH1 H2 IH2].
      - simpl. trivial.
      - simpl. unfold not. intros Heq. inversion Heq.
      - destruct l1 as [| a1 s1]; simpl.
        + apply IH2.
        + simpl in IH1. exact IH1.
    }
    specialize (Hlemma "><<>" Hcb).
    simpl in Hlemma.
    apply Hlemma. reflexivity.
Qed.