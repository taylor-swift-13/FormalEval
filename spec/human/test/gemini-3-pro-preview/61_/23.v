Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii Coq.Strings.String.
Import ListNotations.

Inductive is_correctly_bracketed : list ascii -> Prop :=
  | cb_nil    : is_correctly_bracketed []
  | cb_nest   : forall l,
                  is_correctly_bracketed l ->
                  is_correctly_bracketed ("("%char :: l ++ [")"%char])
  | cb_concat : forall l1 l2,
                  is_correctly_bracketed l1 ->
                  is_correctly_bracketed l2 ->
                  is_correctly_bracketed (l1 ++ l2).

Definition problem_61_pre (brackets : string) : Prop :=
  Forall (fun c => c = "("%char \/ c = ")"%char) (list_ascii_of_string brackets).

Definition problem_61_spec (brackets : list ascii) (b : bool) : Prop :=
  b = true <-> is_correctly_bracketed brackets.

Fixpoint count (c : ascii) (l : list ascii) : nat :=
  match l with
  | [] => 0
  | x :: xs => (if Ascii.ascii_dec x c then 1 else 0) + count c xs
  end.

Lemma count_app : forall c l1 l2, count c (l1 ++ l2) = count c l1 + count c l2.
Proof.
  intros c l1 l2. induction l1 as [|x xs IH].
  - reflexivity.
  - simpl. rewrite IH. apply PeanoNat.Nat.add_assoc.
Qed.

Lemma cb_balance : forall l, is_correctly_bracketed l -> count "("%char l = count ")"%char l.
Proof.
  intros l H. induction H.
  - reflexivity.
  - simpl. rewrite !count_app. simpl.
    rewrite IHis_correctly_bracketed.
    rewrite PeanoNat.Nat.add_0_r.
    rewrite PeanoNat.Nat.add_comm.
    reflexivity.
  - rewrite !count_app. rewrite IHis_correctly_bracketed1. rewrite IHis_correctly_bracketed2. reflexivity.
Qed.

Example test_case_1 : problem_61_spec ["("%char; "("%char; "("%char; ")"%char; ")"%char; "("%char; "("%char; "("%char; ")"%char; ")"%char] false.
Proof.
  unfold problem_61_spec.
  split.
  - intros H. discriminate H.
  - intros H. apply cb_balance in H.
    simpl in H.
    discriminate H.
Qed.