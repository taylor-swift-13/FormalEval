Require Import Coq.Arith.Arith Coq.Bool.Bool Coq.Lists.List.
Require Import Lia.
Import ListNotations.

Inductive digit_7_count_rel : nat -> nat -> Prop :=
| d7c_zero : digit_7_count_rel 0 0
| d7c_mod10_7 : forall n c,
    n mod 10 = 7 ->
    digit_7_count_rel (n / 10) c ->
    digit_7_count_rel n (S c)
| d7c_mod10_other : forall n c,
    n mod 10 <> 7 ->
    digit_7_count_rel (n / 10) c ->
    digit_7_count_rel n c.

Inductive fizz_buzz_rel : nat -> nat -> Prop :=
| fbz_zero : fizz_buzz_rel 0 0
| fbz_next_div : forall n acc c,
    fizz_buzz_rel n acc ->
    (n mod 11 = 0 \/ n mod 13 = 0) ->
    digit_7_count_rel n c ->
    fizz_buzz_rel (S n) (acc + c)
| fbz_next_nodiv : forall n acc,
    fizz_buzz_rel n acc ->
    ~(n mod 11 = 0 \/ n mod 13 = 0) ->
    fizz_buzz_rel (S n) acc.

Definition problem_36_pre (n : nat) : Prop := True.

Definition problem_36_spec (n : nat) (output : nat) : Prop :=
  fizz_buzz_rel n output.

Example test_problem_36_case_50 : problem_36_spec 50 0.
Proof.
  unfold problem_36_spec.
  eapply (fbz_next_nodiv 49 0).
  eapply (fbz_next_nodiv 48 0).
  eapply (fbz_next_nodiv 47 0).
  eapply (fbz_next_nodiv 46 0).
  eapply (fbz_next_nodiv 45 0).
  eapply (fbz_next_div 44 0 0).
  eapply (fbz_next_nodiv 43 0).
  eapply (fbz_next_nodiv 42 0).
  eapply (fbz_next_nodiv 41 0).
  eapply (fbz_next_nodiv 40 0).
  eapply (fbz_next_div 39 0 0).
  eapply (fbz_next_nodiv 38 0).
  eapply (fbz_next_nodiv 37 0).
  eapply (fbz_next_nodiv 36 0).
  eapply (fbz_next_nodiv 35 0).
  eapply (fbz_next_nodiv 34 0).
  eapply (fbz_next_div 33 0 0).
  eapply (fbz_next_nodiv 32 0).
  eapply (fbz_next_nodiv 31 0).
  eapply (fbz_next_nodiv 30 0).
  eapply (fbz_next_nodiv 29 0).
  eapply (fbz_next_nodiv 28 0).
  eapply (fbz_next_nodiv 27 0).
  eapply (fbz_next_div 26 0 0).
  eapply (fbz_next_nodiv 25 0).
  eapply (fbz_next_nodiv 24 0).
  eapply (fbz_next_nodiv 23 0).
  eapply (fbz_next_div 22 0 0).
  eapply (fbz_next_nodiv 21 0).
  eapply (fbz_next_nodiv 20 0).
  eapply (fbz_next_nodiv 19 0).
  eapply (fbz_next_nodiv 18 0).
  eapply (fbz_next_nodiv 17 0).
  eapply (fbz_next_nodiv 16 0).
  eapply (fbz_next_nodiv 15 0).
  eapply (fbz_next_nodiv 14 0).
  eapply (fbz_next_div 13 0 0).
  eapply (fbz_next_nodiv 12 0).
  eapply (fbz_next_div 11 0 0).
  eapply (fbz_next_nodiv 10 0).
  eapply (fbz_next_nodiv 9 0).
  eapply (fbz_next_nodiv 8 0).
  eapply (fbz_next_nodiv 7 0).
  eapply (fbz_next_nodiv 6 0).
  eapply (fbz_next_nodiv 5 0).
  eapply (fbz_next_nodiv 4 0).
  eapply (fbz_next_nodiv 3 0).
  eapply (fbz_next_nodiv 2 0).
  eapply (fbz_next_nodiv 1 0).
  eapply (fbz_next_div 0 0 0).
  apply fbz_zero.
  left. simpl. reflexivity.
  apply d7c_zero.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  left. simpl. reflexivity.
  apply d7c_mod10_other; [simpl; lia|].
  apply d7c_mod10_other; [simpl; lia|].
  apply d7c_zero.
  simpl. unfold not; intros [H|H]; lia.
  right. simpl. reflexivity.
  apply d7c_mod10_other; [simpl; lia|].
  apply d7c_mod10_other; [simpl; lia|].
  apply d7c_zero.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  left. simpl. reflexivity.
  apply d7c_mod10_other; [simpl; lia|].
  apply d7c_mod10_other; [simpl; lia|].
  apply d7c_zero.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  right. simpl. reflexivity.
  apply d7c_mod10_other; [simpl; lia|].
  apply d7c_mod10_other; [simpl; lia|].
  apply d7c_zero.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  left. simpl. reflexivity.
  apply d7c_mod10_other; [simpl; lia|].
  apply d7c_mod10_other; [simpl; lia|].
  apply d7c_zero.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  right. simpl. reflexivity.
  apply d7c_mod10_other; [simpl; lia|].
  apply d7c_mod10_other; [simpl; lia|].
  apply d7c_zero.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  left. simpl. reflexivity.
  apply d7c_mod10_other; [simpl; lia|].
  apply d7c_mod10_other; [simpl; lia|].
  apply d7c_zero.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
  simpl. unfold not; intros [H|H]; lia.
Qed.