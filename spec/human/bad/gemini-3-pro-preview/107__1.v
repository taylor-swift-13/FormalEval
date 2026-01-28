Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* Specification definitions *)

Inductive to_digits_rel : nat -> list nat -> Prop :=
| tdr_zero : to_digits_rel 0%nat nil
| tdr_step : forall n d ds, n > 0 -> d = n mod 10 ->
    to_digits_rel (n / 10) ds ->
    to_digits_rel n (d :: ds).

Inductive is_palindrome_rel : nat -> Prop :=
| ipr_pal : forall n ds, n > 0 -> to_digits_rel n ds -> ds = rev ds -> is_palindrome_rel n.

Inductive is_even_rel : nat -> Prop :=
| ier_even : forall n, n mod 2 = 0 -> is_even_rel n.

Inductive is_even_pal_rel : nat -> Prop :=
| iepr_build : forall n, is_palindrome_rel n -> is_even_rel n -> is_even_pal_rel n.

Inductive is_odd_pal_rel : nat -> Prop :=
| iopr_build : forall n, is_palindrome_rel n -> ~ is_even_rel n -> is_odd_pal_rel n.

Inductive count_in_range_rel : (nat -> Prop) -> nat -> nat -> Prop :=
| cir_zero : forall (P : nat -> Prop), count_in_range_rel P 0%nat 0%nat
| cir_hit : forall (P : nat -> Prop) k n, P (S k) -> count_in_range_rel P k n ->
   count_in_range_rel P (S k) (S n)
| cir_miss : forall (P : nat -> Prop) k n, ~ P (S k) -> count_in_range_rel P k n ->
   count_in_range_rel P (S k) n.

Definition problem_107_pre (n : nat) : Prop := n > 0.

Definition problem_107_spec (n : nat) (output : nat * nat) : Prop :=
  let '(e, o) := output in
  count_in_range_rel is_even_pal_rel n e /\
  count_in_range_rel is_odd_pal_rel n o.

(* Proof Implementation *)

(* 1. Computable Digits Function *)

Fixpoint digits_f (fuel n : nat) : list nat :=
  match fuel with
  | 0 => nil
  | S f => match n with
           | 0 => nil
           | _ => (n mod 10) :: digits_f f (n / 10)
           end
  end.

Definition digits (n : nat) : list nat := digits_f (S n) n.

Lemma digits_f_correct : forall fuel n, n < fuel -> to_digits_rel n (digits_f fuel n).
Proof.
  induction fuel; intros.
  - lia.
  - simpl. destruct n.
    + apply tdr_zero.
    + apply tdr_step.
      * lia.
      * reflexivity.
      * apply IHfuel.
        assert (S n / 10 < S n). {
          destruct (lt_dec (S n) 10).
          - rewrite Nat.div_small; auto. lia.
          - apply Nat.div_lt; lia.
        }
        lia.
Qed.

Lemma digits_correct : forall n, to_digits_rel n (digits n).
Proof.
  intros. apply digits_f_correct. lia.
Qed.

Lemma to_digits_rel_det : forall n l1 l2,
  to_digits_rel n l1 -> to_digits_rel n l2 -> l1 = l2.
Proof.
  intros n l1 l2 H1. revert l2.
  induction H1; intros l2 H2.
  - inversion H2; subst; auto. lia.
  - inversion H2; subst.
    + lia.
    + assert (ds = ds0) by (apply IHto_digits_rel; auto). subst. auto.
Qed.

(* 2. Boolean Checkers *)

Definition list_eq_dec_nat : forall (l1 l2 : list nat), {l1 = l2} + {l1 <> l2}.
Proof. apply list_eq_dec. apply Nat.eq_dec. Defined.

Definition is_pal_b (n : nat) : bool :=
  let d := digits n in
  (n >? 0) && (if list_eq_dec_nat d (rev d) then true else false).

Lemma is_pal_reflect : forall n, is_palindrome_rel n <-> is_pal_b n = true.
Proof.
  intros. unfold is_pal_b.
  split; intro H.
  - destruct H as [n ds Hn Hrel Hrev].
    apply andb_true_intro. split.
    + apply Nat.leb_le. lia.
    + destruct (list_eq_dec_nat (digits n) (rev (digits n))).
      * reflexivity.
      * exfalso. apply n0.
        assert (digits n = ds). { apply to_digits_rel_det with n; auto. apply digits_correct. }
        subst. auto.
  - apply andb_true_iff in H. destruct H as [Hn Hrev].
    apply Nat.leb_le in Hn.
    destruct (list_eq_dec_nat (digits n) (rev (digits n))) in Hrev; try discriminate.
    econstructor.
    + apply Hn.
    + apply digits_correct.
    + apply e.
Qed.

Definition is_even_b (n : nat) : bool := (n mod 2 =? 0).

Lemma is_even_reflect : forall n, is_even_rel n <-> is_even_b n = true.
Proof.
  intros. unfold is_even_b. split; intro H.
  - destruct H. apply Nat.eqb_eq. auto.
  - apply ier_even. apply Nat.eqb_eq. auto.
Qed.

Definition is_even_pal_b (n : nat) : bool := is_pal_b n && is_even_b n.
Definition is_odd_pal_b (n : nat) : bool := is_pal_b n && negb (is_even_b n).

Lemma is_even_pal_reflect : forall n, is_even_pal_rel n <-> is_even_pal_b n = true.
Proof.
  intros. unfold is_even_pal_b. split; intro H.
  - destruct H. apply andb_true_intro. split.
    + apply is_pal_reflect; auto.
    + apply is_even_reflect; auto.
  - apply andb_true_iff in H. destruct H.
    constructor.
    + apply is_pal_reflect; auto.
    + apply is_even_reflect; auto.
Qed.

Lemma is_odd_pal_reflect : forall n, is_odd_pal_rel n <-> is_odd_pal_b n = true.
Proof.
  intros. unfold is_odd_pal_b. split; intro H.
  - destruct H. apply andb_true_intro. split.
    + apply is_pal_reflect; auto.
    + apply negb_true_iff. destruct (is_even_b n) eqn:E; auto.
      apply is_even_reflect in E. contradiction.
  - apply andb_true_iff in H. destruct H as [Hp He].
    apply negb_true_iff in He.
    constructor.
    + apply is_pal_reflect; auto.
    + intro. apply is_even_reflect in H. congruence.
Qed.

(* 3. Counting Logic *)

Fixpoint count_f (p : nat -> bool) (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => (if p (S k) then 1 else 0) + count_f p k
  end.

Lemma count_correct : forall (P : nat -> Prop) (p : nat -> bool) (n : nat),
  (forall k, k <= n -> (P k <-> p k = true)) ->
  count_in_range_rel P n (count_f p n).
Proof.
  intros P p n Href.
  induction n.
  - simpl. constructor.
  - simpl. destruct (p (S n)) eqn:Hp.
    + apply cir_hit.
      * apply Href. lia. auto.
      * apply IHn. intros. apply Href. lia.
    + apply cir_miss.
      * rewrite Href; [congruence | lia].
      * apply IHn. intros. apply Href. lia.
Qed.

(* 4. Test Case Proof *)

Example test_case_proof : problem_107_spec 123 (8, 13).
Proof.
  unfold problem_107_spec.
  split.
  - replace 8 with (count_f is_even_pal_b 123) by (vm_compute; reflexivity).
    apply count_correct.
    intros. apply is_even_pal_reflect.
  - replace 13 with (count_f is_odd_pal_b 123) by (vm_compute; reflexivity).
    apply count_correct.
    intros. apply is_odd_pal_reflect.
Qed.