Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

(* Inductive definition of correctly bracketed strings *)
Inductive is_correctly_bracketed : string -> Prop :=
  | cb_nil    : is_correctly_bracketed ""
  | cb_nest   : forall l,
                  is_correctly_bracketed l ->
                  is_correctly_bracketed ("<" ++ l ++ ">")
  | cb_concat : forall l1 l2,
                  is_correctly_bracketed l1 ->
                  is_correctly_bracketed l2 ->
                  is_correctly_bracketed (l1 ++ l2).

(* Precondition definition *)
Definition problem_56_pre (brackets : string) : Prop :=
    Forall (fun c => c = "<"%char \/ c = ">"%char) (list_ascii_of_string brackets).

(* Specification definition *)
Definition problem_56_spec (brackets : string) (b : bool) : Prop :=
  b = true <-> is_correctly_bracketed brackets.

(* Helper lemma: any non-empty correctly bracketed string must start with '<' *)
Lemma cb_starts_with_open : forall s, is_correctly_bracketed s -> 
  s = "" \/ exists s', s = "<" ++ s'.
Proof.
  intros s H.
  induction H.
  - left. reflexivity.
  - right. exists (l ++ ">"). reflexivity.
  - destruct IHis_correctly_bracketed1 as [Hl1 | Hl1].
    + subst l1. simpl. assumption.
    + right. destruct Hl1 as [s' Heq]. subst l1.
      exists (s' ++ l2). simpl. reflexivity.
Qed.

(* Example Proof for Test Case: input = "><<><><><>>>><><", output = false *)
Example test_correct_bracketing_fail : problem_56_spec "><<><><><>>>><><" false.
Proof.
  unfold problem_56_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    apply cb_starts_with_open in H.
    destruct H as [Hempty | [s' Hstart]].
    + discriminate Hempty.
    + discriminate Hstart.
Qed.