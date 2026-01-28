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

(* Helper functions for proof *)
Fixpoint count_open (s : string) : nat :=
  match s with
  | "" => 0
  | String c s' => (if Ascii.ascii_dec c "<"%char then 1 else 0) + count_open s'
  end.

Fixpoint count_close (s : string) : nat :=
  match s with
  | "" => 0
  | String c s' => (if Ascii.ascii_dec c ">"%char then 1 else 0) + count_close s'
  end.

Lemma count_open_app : forall s1 s2, count_open (s1 ++ s2) = count_open s1 + count_open s2.
Proof.
  induction s1; intros; simpl; auto.
  destruct (Ascii.ascii_dec a "<"%char); rewrite IHs1; auto.
Qed.

Lemma count_close_app : forall s1 s2, count_close (s1 ++ s2) = count_close s1 + count_close s2.
Proof.
  induction s1; intros; simpl; auto.
  destruct (Ascii.ascii_dec a ">"%char); rewrite IHs1; auto.
Qed.

Lemma cb_counts_eq : forall s, is_correctly_bracketed s -> count_open s = count_close s.
Proof.
  intros s H. induction H.
  - reflexivity.
  - rewrite count_open_app, count_close_app.
    simpl.
    rewrite count_open_app, count_close_app.
    simpl.
    rewrite IHis_correctly_bracketed.
    ring.
  - rewrite count_open_app, count_close_app.
    rewrite IHis_correctly_bracketed1, IHis_correctly_bracketed2.
    reflexivity.
Qed.

(* Example Proof for Test Case: input = "<><><<><>><>>><>", output = false *)
Example test_problem_56 : problem_56_spec "<><><<><>><>>><>" false.
Proof.
  unfold problem_56_spec.
  split.
  - intros H. discriminate.
  - intros H. apply cb_counts_eq in H.
    vm_compute in H. discriminate.
Qed.