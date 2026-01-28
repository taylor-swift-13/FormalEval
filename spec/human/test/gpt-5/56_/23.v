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
  problem_56_spec "<<<<>><>>><>" true.
Proof.
  unfold problem_56_spec.
  split.
  - intros _.
    assert (H0: "<" ++ "" ++ ">" = "<>") by reflexivity.
    assert (H2: (("<" ++ "<<<>><>>" ++ ">") ++ "<>") = "<<<<>><>>><>") by reflexivity.
    rewrite <- H2.
    apply cb_concat.
    + apply cb_nest.
      assert (H3: "<" ++ "<<>><>" ++ ">" = "<<<>><>>") by reflexivity.
      rewrite <- H3.
      apply cb_nest.
      assert (H4: "<<>>" ++ "<>" = "<<>><>") by reflexivity.
      rewrite <- H4.
      apply cb_concat.
      * assert (H5: "<" ++ "<>" ++ ">" = "<<>>") by reflexivity.
        rewrite <- H5.
        apply cb_nest.
        rewrite <- H0.
        apply cb_nest.
        apply cb_nil.
      * rewrite <- H0.
        apply cb_nest.
        apply cb_nil.
    + rewrite <- H0.
      apply cb_nest.
      apply cb_nil.
  - intros _. reflexivity.
Qed.