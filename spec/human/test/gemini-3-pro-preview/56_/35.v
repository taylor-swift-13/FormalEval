Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
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

(* Auxiliary definitions for the proof *)
Fixpoint count (target : ascii) (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => (if Ascii.eqb c target then 1 else 0) + count target s'
  end.

Lemma count_append : forall target s1 s2, count target (s1 ++ s2) = count target s1 + count target s2.
Proof.
  intros target s1 s2. induction s1 as [|c s1 IH].
  - reflexivity.
  - simpl. rewrite IH. apply Nat.add_assoc.
Qed.

Lemma cb_equal_counts : forall s, is_correctly_bracketed s -> count "<" s = count ">" s.
Proof.
  intros s H. induction H.
  - reflexivity.
  - simpl. repeat rewrite count_append. simpl.
    rewrite IHis_correctly_bracketed.
    rewrite Nat.add_0_r. rewrite Nat.add_comm. reflexivity.
  - repeat rewrite count_append. rewrite IHis_correctly_bracketed1. rewrite IHis_correctly_bracketed2. reflexivity.
Qed.

(* Example Proof for Test Case: input = "<<<>", output = false *)
Example test_incorrect_bracketing : problem_56_spec "<<<>" false.
Proof.
  unfold problem_56_spec.
  split; intros H.
  - discriminate H.
  - apply cb_equal_counts in H.
    simpl in H.
    discriminate H.
Qed.