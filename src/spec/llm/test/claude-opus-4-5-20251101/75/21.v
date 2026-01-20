Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n > 1 /\ forall d : Z, 1 < d < n -> Z.rem n d <> 0.

Inductive prime_factorization : Z -> list Z -> Prop :=
  | pf_one : prime_factorization 1 []
  | pf_cons : forall n p rest,
      n > 1 ->
      is_prime p ->
      Z.rem n p = 0 ->
      prime_factorization (Z.div n p) rest ->
      prime_factorization n (p :: rest).

Definition is_multiply_prime_spec (a : Z) (result : bool) : Prop :=
  (result = true <->
    (a > 1 /\
     exists p1 p2 p3 : Z,
       is_prime p1 /\ is_prime p2 /\ is_prime p3 /\
       a = p1 * p2 * p3)) /\
  (result = false <->
    (a <= 1 \/
     ~(exists p1 p2 p3 : Z,
         is_prime p1 /\ is_prime p2 /\ is_prime p3 /\
         a = p1 * p2 * p3))).

Lemma prime_ge_2 : forall p, is_prime p -> p >= 2.
Proof.
  intros p [Hp _]. lia.
Qed.

Lemma product_of_three_primes_ge_8 : forall p1 p2 p3,
  is_prime p1 -> is_prime p2 -> is_prime p3 ->
  p1 * p2 * p3 >= 8.
Proof.
  intros p1 p2 p3 H1 H2 H3.
  assert (p1 >= 2) by (apply prime_ge_2; auto).
  assert (p2 >= 2) by (apply prime_ge_2; auto).
  assert (p3 >= 2) by (apply prime_ge_2; auto).
  nia.
Qed.

Example test_is_multiply_prime_19 : is_multiply_prime_spec 19 false.
Proof.
  unfold is_multiply_prime_spec.
  split.
  - split.
    + intros H. discriminate H.
    + intros [Hgt [p1 [p2 [p3 [Hp1 [Hp2 [Hp3 Heq]]]]]]].
      assert (Hp1_ge : p1 >= 2) by (apply prime_ge_2; auto).
      assert (Hp2_ge : p2 >= 2) by (apply prime_ge_2; auto).
      assert (Hp3_ge : p3 >= 2) by (apply prime_ge_2; auto).
      assert (p1 * p2 * p3 >= 8) by nia.
      assert (p1 * p2 >= 4) by nia.
      assert (p1 * p2 * p3 >= 2 * 2 * 2) by nia.
      destruct (Z.eq_dec p1 2); destruct (Z.eq_dec p2 2); destruct (Z.eq_dec p3 2).
      * subst. simpl in Heq. lia.
      * subst. assert (p3 >= 3) by lia. nia.
      * subst. assert (p2 >= 3) by lia. nia.
      * subst. assert (p2 >= 3) by lia. assert (p3 >= 3) by lia. nia.
      * subst. assert (p1 >= 3) by lia. nia.
      * subst. assert (p1 >= 3) by lia. assert (p3 >= 3) by lia. nia.
      * subst. assert (p1 >= 3) by lia. assert (p2 >= 3) by lia. nia.
      * assert (p1 >= 3) by lia. assert (p2 >= 3) by lia. assert (p3 >= 3) by lia. nia.
  - split.
    + intros _.
      right.
      intros [p1 [p2 [p3 [Hp1 [Hp2 [Hp3 Heq]]]]]].
      assert (Hp1_ge : p1 >= 2) by (apply prime_ge_2; auto).
      assert (Hp2_ge : p2 >= 2) by (apply prime_ge_2; auto).
      assert (Hp3_ge : p3 >= 2) by (apply prime_ge_2; auto).
      destruct (Z.eq_dec p1 2); destruct (Z.eq_dec p2 2); destruct (Z.eq_dec p3 2).
      * subst. simpl in Heq. lia.
      * subst. assert (p3 >= 3) by lia. nia.
      * subst. assert (p2 >= 3) by lia. nia.
      * subst. assert (p2 >= 3) by lia. assert (p3 >= 3) by lia. nia.
      * subst. assert (p1 >= 3) by lia. nia.
      * subst. assert (p1 >= 3) by lia. assert (p3 >= 3) by lia. nia.
      * subst. assert (p1 >= 3) by lia. assert (p2 >= 3) by lia. nia.
      * assert (p1 >= 3) by lia. assert (p2 >= 3) by lia. assert (p3 >= 3) by lia. nia.
    + intros _. reflexivity.
Qed.