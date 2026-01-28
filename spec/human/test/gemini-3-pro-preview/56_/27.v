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

(* Helper definitions for the proof *)
Fixpoint count (c : ascii) (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c' s' => (if Ascii.ascii_dec c c' then 1 else 0) + count c s'
  end.

Lemma count_append : forall c s1 s2, count c (s1 ++ s2) = count c s1 + count c s2.
Proof.
  intros c s1 s2. induction s1 as [| c' s1' IH].
  - reflexivity.
  - simpl. destruct (Ascii.ascii_dec c c'); rewrite IH; auto.
Qed.

Lemma cb_balance : forall s, is_correctly_bracketed s -> count "<" s = count ">" s.
Proof.
  intros s H. induction H.
  - reflexivity.
  - simpl. repeat rewrite count_append. simpl.
    destruct (Ascii.ascii_dec "<" "<"); [|contradiction].
    destruct (Ascii.ascii_dec ">" "<"); [discriminate|].
    destruct (Ascii.ascii_dec "<" ">"); [discriminate|].
    destruct (Ascii.ascii_dec ">" ">"); [|contradiction].
    simpl. rewrite IHis_correctly_bracketed.
    rewrite Nat.add_0_r. rewrite Nat.add_1_r. reflexivity.
  - rewrite !count_append. rewrite IHis_correctly_bracketed1, IHis_correctly_bracketed2. reflexivity.
Qed.

Example test_correct_bracketing_false : problem_56_spec "<<><<" false.
Proof.
  unfold problem_56_spec.
  split.
  - intros H. inversion H.
  - intros H.
    apply cb_balance in H.
    simpl in H.
    discriminate.
Qed.