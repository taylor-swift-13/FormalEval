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

(* Helper Lemma: A non-empty correctly bracketed string must start with '<' *)
Lemma correct_starts_with_open : forall s,
  is_correctly_bracketed s ->
  match s with
  | EmptyString => True
  | String c _ => c = "<"%char
  end.
Proof.
  intros s H. induction H.
  - (* cb_nil *)
    simpl. trivial.
  - (* cb_nest *)
    simpl. reflexivity.
  - (* cb_concat *)
    destruct l1.
    + (* l1 is empty *)
      simpl in *. apply IHis_correctly_bracketed2.
    + (* l1 is not empty *)
      simpl in *. apply IHis_correctly_bracketed1.
Qed.

(* Example Proof for Test Case: input = "><<<<<>>", output = false *)
Example test_correct_bracketing_incorrect : problem_56_spec "><<<<<>>" false.
Proof.
  unfold problem_56_spec.
  split.
  - (* Direction: false = true -> ... *)
    intros H.
    discriminate.
  - (* Direction: is_correctly_bracketed "><<<<<>>" -> false = true *)
    intros H.
    (* Apply the helper lemma *)
    apply correct_starts_with_open in H.
    (* Simplify the match on the concrete string *)
    simpl in H.
    (* H becomes ">" = "<", which is a contradiction *)
    discriminate.
Qed.