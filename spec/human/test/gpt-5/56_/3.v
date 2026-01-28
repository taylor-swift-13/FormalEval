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
  problem_56_spec "<><><<><>><>" true.
Proof.
  unfold problem_56_spec.
  split.
  - intros _.
    assert (H0: "<" ++ "" ++ ">" = "<>") by reflexivity.
    assert (Hpair: "<>" ++ "<>" = "<><>") by reflexivity.
    assert (Hnest: "<" ++ "<><>" ++ ">" = "<<><>>") by reflexivity.
    assert (Hsplit1: "<><>" ++ "<<><>>" = "<><><<><>>") by reflexivity.
    assert (Hsplit2: "<><><<><>>" ++ "<>" = "<><><<><>><>") by reflexivity.
    rewrite <- Hsplit2.
    apply cb_concat.
    + rewrite <- Hsplit1.
      apply cb_concat.
      * rewrite <- Hpair.
        apply cb_concat.
        -- rewrite <- H0. apply cb_nest. apply cb_nil.
        -- rewrite <- H0. apply cb_nest. apply cb_nil.
      * rewrite <- Hnest.
        apply cb_nest.
        rewrite <- Hpair.
        apply cb_concat.
        -- rewrite <- H0. apply cb_nest. apply cb_nil.
        -- rewrite <- H0. apply cb_nest. apply cb_nil.
    + rewrite <- H0. apply cb_nest. apply cb_nil.
  - intros _. reflexivity.
Qed.