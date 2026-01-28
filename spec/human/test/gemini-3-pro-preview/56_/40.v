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

(* Helper definition to identify strings starting with '>' *)
Definition starts_with_gt (s : string) : Prop :=
  match s with
  | String ">" _ => True
  | _ => False
  end.

(* Lemma: A correctly bracketed string cannot start with '>' *)
Lemma cb_not_start_gt : forall s, is_correctly_bracketed s -> starts_with_gt s -> False.
Proof.
  intros s H.
  induction H.
  - (* cb_nil *)
    simpl. auto.
  - (* cb_nest *)
    simpl. auto.
  - (* cb_concat *)
    unfold starts_with_gt in *.
    intros Hstart.
    destruct l1.
    + (* l1 is empty, check l2 *)
      simpl in Hstart.
      apply IHis_correctly_bracketed2.
      assumption.
    + (* l1 is not empty, check l1 *)
      simpl in Hstart.
      apply IHis_correctly_bracketed1.
      assumption.
Qed.

(* Example Proof for Test Case: input = ">>>><<...", output = false *)
Example test_correct_bracketing_fail : 
  problem_56_spec ">>>><<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<" false.
Proof.
  unfold problem_56_spec.
  split.
  - (* Direction: false = true -> is_correctly_bracketed ... *)
    intros H.
    discriminate H.
  - (* Direction: is_correctly_bracketed ... -> false = true *)
    intros H.
    exfalso.
    apply (cb_not_start_gt _ H).
    simpl.
    exact I.
Qed.