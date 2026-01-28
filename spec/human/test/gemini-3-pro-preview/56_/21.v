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

(* Helper function to extract the first character *)
Definition head_opt (s : string) : option ascii :=
  match s with
  | EmptyString => None
  | String c _ => Some c
  end.

(* Lemma: A correctly bracketed string cannot start with '>' *)
Lemma cb_head_not_close : forall s,
  is_correctly_bracketed s -> head_opt s = Some ">"%char -> False.
Proof.
  intros s H. induction H.
  - (* cb_nil *)
    simpl. discriminate.
  - (* cb_nest *)
    simpl. intros Hinv. inversion Hinv.
  - (* cb_concat *)
    simpl. destruct l1.
    + (* l1 is empty *)
      simpl. apply IHis_correctly_bracketed2.
    + (* l1 is not empty *)
      simpl. apply IHis_correctly_bracketed1.
Qed.

(* Test Case: input = ">>>><<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<", output = false *)
Example test_correct_bracketing_fail : 
  problem_56_spec ">>>><<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<" false.
Proof.
  unfold problem_56_spec.
  split.
  - (* Direction: false = true -> is_correctly_bracketed ... *)
    intros H. discriminate H.
  - (* Direction: is_correctly_bracketed ... -> false = true *)
    intros H.
    exfalso.
    apply (cb_head_not_close ">>>><<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<").
    * exact H.
    * reflexivity.
Qed.