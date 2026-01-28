Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
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

Fixpoint count_char (c : ascii) (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String a s' => (if Ascii.ascii_dec a c then 1 else 0) + count_char c s'
  end.

Lemma count_char_app : forall c s1 s2,
  count_char c (s1 ++ s2) = count_char c s1 + count_char c s2.
Proof.
  intros c s1; induction s1 as [| a s1' IH]; intros s2; simpl.
  - reflexivity.
  - simpl. destruct (Ascii.ascii_dec a c).
    + rewrite IH. rewrite Nat.add_assoc. reflexivity.
    + rewrite IH. rewrite Nat.add_assoc. reflexivity.
Qed.

Lemma cb_counts : forall s, is_correctly_bracketed s -> count_char "<"%char s = count_char ">"%char s.
Proof.
  intros s H; induction H as [| l Hl IH | l1 l2 Hl1 IH1 Hl2 IH2].
  - simpl. reflexivity.
  - rewrite count_char_app. rewrite count_char_app. simpl.
    rewrite IH. rewrite Nat.add_0_r. rewrite Nat.add_0_l.
    rewrite Nat.add_comm. reflexivity.
  - rewrite count_char_app. rewrite count_char_app. rewrite IH1. rewrite IH2. reflexivity.
Qed.

Example problem_56_test_case_1 :
  problem_56_spec "<<<" false.
Proof.
  unfold problem_56_spec.
  split.
  - intros H. discriminate H.
  - intros Hcb.
    pose proof (cb_counts "<<<" Hcb) as Hcnt.
    simpl in Hcnt.
    exfalso. discriminate Hcnt.
Qed.