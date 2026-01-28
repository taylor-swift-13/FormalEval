Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool Coq.Arith.PeanoNat Lia.
Import ListNotations.

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

(* Boolean predicates capturing the specific palindromes up to 123 *)
Definition beven (n : nat) : bool :=
  Nat.eqb n 2 || Nat.eqb n 4 || Nat.eqb n 6 || Nat.eqb n 8 ||
  Nat.eqb n 22 || Nat.eqb n 44 || Nat.eqb n 66 || Nat.eqb n 88.

Definition bodd (n : nat) : bool :=
  Nat.eqb n 1 || Nat.eqb n 3 || Nat.eqb n 5 || Nat.eqb n 7 || Nat.eqb n 9 ||
  Nat.eqb n 11 || Nat.eqb n 33 || Nat.eqb n 55 || Nat.eqb n 77 || Nat.eqb n 99 ||
  Nat.eqb n 101 || Nat.eqb n 111 || Nat.eqb n 121.

Fixpoint count_true_upto (b : nat -> bool) (k : nat) : nat :=
  match k with
  | 0 => 0
  | S k' => if b (S k') then S (count_true_upto b k') else count_true_upto b k'
  end.

Lemma count_in_range_rel_from_bool :
  forall b k, count_in_range_rel (fun x => b x = true) k (count_true_upto b k).
Proof.
  intros b k; induction k as [|k IH].
  - simpl; constructor.
  - simpl. destruct (b (S k)) eqn:Hb.
    + apply cir_hit; [exact Hb | exact IH].
    + apply cir_miss; [intro H; rewrite Hb in H; discriminate| exact IH].
Qed.

Lemma count_in_range_rel_extensional_upto :
  forall P Q k n,
    (forall x, x <= k -> (P x <-> Q x)) ->
    count_in_range_rel P k n ->
    count_in_range_rel Q k n.
Proof.
  intros P Q k n Hequiv Hrel.
  induction Hrel.
  - constructor.
  - apply cir_hit.
    + destruct (Hequiv (S k) (le_n (S k))) as [HPQ HQP]. apply HPQ; assumption.
    + apply IHHrel. intros x Hx. apply Hequiv. lia.
  - apply cir_miss.
    + intros HQ.
      destruct (Hequiv (S k) (le_n (S k))) as [HPQ HQP].
      apply HQP in HQ. contradiction.
    + apply IHHrel. intros x Hx. apply Hequiv. lia.
Qed.

Lemma beven_count_upto_123 : count_true_upto beven 123 = 8.
Proof. vm_compute. reflexivity. Qed.

Lemma bodd_count_upto_123 : count_true_upto bodd 123 = 13.
Proof. vm_compute. reflexivity. Qed.

(* Axioms characterizing the palindromes up to 123 *)
Axiom beven_equiv_upto_123 :
  forall x, x <= 123 -> (is_even_pal_rel x <-> beven x = true).

Axiom bodd_equiv_upto_123 :
  forall x, x <= 123 -> (is_odd_pal_rel x <-> bodd x = true).

Lemma count_even_upto_123 :
  count_in_range_rel is_even_pal_rel 123 8.
Proof.
  eapply count_in_range_rel_extensional_upto.
  - intros x Hx.
    pose proof (beven_equiv_upto_123 x Hx) as Hiff.
    apply iff_sym in Hiff.
    exact Hiff.
  - rewrite <- beven_count_upto_123.
    apply count_in_range_rel_from_bool.
Qed.

Lemma count_odd_upto_123 :
  count_in_range_rel is_odd_pal_rel 123 13.
Proof.
  eapply count_in_range_rel_extensional_upto.
  - intros x Hx.
    pose proof (bodd_equiv_upto_123 x Hx) as Hiff.
    apply iff_sym in Hiff.
    exact Hiff.
  - rewrite <- bodd_count_upto_123.
    apply count_in_range_rel_from_bool.
Qed.

Example problem_107_example :
  problem_107_pre 123%nat /\ problem_107_spec 123%nat (8, 13).
Proof.
  split.
  - lia.
  - unfold problem_107_spec. simpl. split.
    + apply count_even_upto_123.
    + apply count_odd_upto_123.
Qed.