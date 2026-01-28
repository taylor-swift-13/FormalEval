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

(* Helper Lemma: A correctly bracketed string is either empty or starts with '<' *)
Lemma cb_starts_with_open_or_empty : forall s, 
  is_correctly_bracketed s -> 
  s = "" \/ exists s', s = "<" ++ s'.
Proof.
  intros s H.
  induction H.
  - (* cb_nil *)
    left. reflexivity.
  - (* cb_nest *)
    right. exists (l ++ ">"). reflexivity.
  - (* cb_concat *)
    destruct IHis_correctly_bracketed1 as [H_l1_nil | [s_l1_tail H_l1_start]].
    + (* l1 is empty *)
      subst l1. simpl. apply IHis_correctly_bracketed2.
    + (* l1 starts with < *)
      right. subst l1. 
      exists (s_l1_tail ++ l2). reflexivity.
Qed.

(* Example Proof for Test Case: input = "><", output = false *)
Example test_incorrect_bracketing : problem_56_spec "><" false.
Proof.
  unfold problem_56_spec.
  split.
  - (* Direction: false = true -> ... *)
    intros H. discriminate H.
  - (* Direction: is_correctly_bracketed "><" -> false = true *)
    intros H.
    apply cb_starts_with_open_or_empty in H.
    destruct H as [H_nil | [s_tail H_start]].
    + (* Case: "><" = "" *)
      discriminate H_nil.
    + (* Case: "><" starts with "<" *)
      (* This implies ">" = "<" which is a contradiction *)
      inversion H_start.
Qed.