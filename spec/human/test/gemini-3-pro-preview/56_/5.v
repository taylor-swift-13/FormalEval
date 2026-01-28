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

(* Helper function to count character occurrences *)
Fixpoint count_char (c : ascii) (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String a s' => (if Ascii.eqb a c then 1 else 0) + count_char c s'
  end.

(* Lemma: count distributes over append *)
Lemma count_char_app : forall c s1 s2,
  count_char c (s1 ++ s2) = count_char c s1 + count_char c s2.
Proof.
  intros c s1 s2. induction s1 as [|a s1 IH].
  - reflexivity.
  - simpl. rewrite IH. apply Nat.add_assoc.
Qed.

(* Lemma: correctly bracketed strings have equal number of < and > *)
Lemma correct_bracketing_counts : forall s,
  is_correctly_bracketed s ->
  count_char "<" s = count_char ">" s.
Proof.
  intros s H. induction H.
  - reflexivity.
  - simpl. repeat rewrite count_char_app. simpl.
    rewrite IHis_correctly_bracketed.
    replace (Ascii.eqb "<" "<") with true by reflexivity.
    replace (Ascii.eqb ">" "<") with false by reflexivity.
    replace (Ascii.eqb "<" ">") with false by reflexivity.
    replace (Ascii.eqb ">" ">") with true by reflexivity.
    simpl. rewrite Nat.add_0_r. rewrite Nat.add_comm. simpl. reflexivity.
  - repeat rewrite count_char_app.
    rewrite IHis_correctly_bracketed1.
    rewrite IHis_correctly_bracketed2.
    reflexivity.
Qed.

(* Example Proof for Test Case: input = "<<<><>>>>", output = false *)
Example test_correct_bracketing_fail : problem_56_spec "<<<><>>>>" false.
Proof.
  unfold problem_56_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    apply correct_bracketing_counts in H.
    vm_compute in H.
    discriminate H.
Qed.