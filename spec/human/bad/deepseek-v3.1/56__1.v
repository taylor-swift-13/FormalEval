Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.
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

Fixpoint correct_bracketing_aux (s : string) (count : nat) : bool :=
  match s with
  | "" => Nat.eqb count 0
  | String c rest =>
      if ascii_dec c "<"%char then
        correct_bracketing_aux rest (S count)
      else if ascii_dec c ">"%char then
        match count with
        | O => false
        | S n => correct_bracketing_aux rest n
        end
      else false
  end.

Definition correct_bracketing (brackets : string) : bool :=
  correct_bracketing_aux brackets 0.

Lemma correct_bracketing_empty : correct_bracketing "" = true.
Proof. simpl. reflexivity. Qed.

Lemma correct_bracketing_nest : forall s,
  correct_bracketing s = true -> correct_bracketing ("<" ++ s ++ ">") = true.
Proof.
  intros s H.
  unfold correct_bracketing.
  simpl.
  rewrite H.
  simpl.
  reflexivity.
Qed.

Lemma correct_bracketing_concat : forall s1 s2,
  correct_bracketing s1 = true -> correct_bracketing s2 = true -> 
  correct_bracketing (s1 ++ s2) = true.
Proof.
  intros s1 s2 H1 H2.
  unfold correct_bracketing in *.
  generalize dependent s2.
  induction s1 as [|c s1 IH] using rev_ind; intros s2 H1 H2.
  - simpl. assumption.
  - rewrite <- app_comm_cons in H1.
    simpl in H1.
    destruct c; simpl in H1.
    + destruct (ascii_dec a "<"%char).
      * subst. simpl in H1.
        specialize (IH s2 H1 H2).
        simpl. rewrite IH. reflexivity.
      * destruct (ascii_dec a ">"%char).
        { subst. simpl in H1.
          destruct (correct_bracketing_aux s1 0) eqn:Haux.
          - simpl in H1. discriminate.
          - discriminate. }
        { discriminate. }
    + destruct (ascii_dec a ">"%char).
      * subst. simpl in H1.
        destruct (correct_bracketing_aux s1 1) eqn:Haux.
        - simpl in H1. discriminate.
        - discriminate.
      * destruct (ascii_dec a "<"%char).
        { subst. simpl in H1. discriminate. }
        { discriminate. }
Qed.

Lemma correct_bracketing_spec : forall s,
  correct_bracketing s = true <-> is_correctly_bracketed s.
Proof.
  intros s. split.
  - intro H.
    induction s as [|c s IH] using rev_ind.
    + apply cb_nil.
    + destruct c; simpl in H.
      * destruct (ascii_dec a "<"%char).
        { subst. simpl in H.
          apply cb_concat with (l1 := "<") (l2 := s).
          - apply cb_nest. apply cb_nil.
          - apply IH. assumption. }
        { destruct (ascii_dec a ">"%char).
          { subst. simpl in H.
            destruct (correct_bracketing_aux s 0) eqn:Haux.
            - apply cb_concat with (l1 := "<>") (l2 := s).
              + apply cb_nest. apply cb_nil.
              + apply IH. assumption.
            - discriminate. }
          { discriminate. } }
  - intro H. induction H.
    + apply correct_bracketing_empty.
    + apply correct_bracketing_nest. assumption.
    + apply correct_bracketing_concat; assumption.
Qed.

Example test_correct_bracketing : correct_bracketing "<>" = true.
Proof.
  simpl. reflexivity.
Qed.

Example test_correct_bracketing_spec : problem_56_spec "<>" true.
Proof.
  unfold problem_56_spec.
  split.
  - intro H. inversion H. 
    apply correct_bracketing_spec. reflexivity.
  - intro H. 
    apply correct_bracketing_spec in H.
    reflexivity.
Qed.