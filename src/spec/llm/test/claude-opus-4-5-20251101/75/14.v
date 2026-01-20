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

Lemma no_three_prime_factorization_21 :
  ~(exists p1 p2 p3 : Z, is_prime p1 /\ is_prime p2 /\ is_prime p3 /\ 21 = p1 * p2 * p3).
Proof.
  intros [p1 [p2 [p3 [Hp1 [Hp2 [Hp3 Heq]]]]]].
  assert (Hge1 : p1 >= 2) by (apply prime_ge_2; auto).
  assert (Hge2 : p2 >= 2) by (apply prime_ge_2; auto).
  assert (Hge3 : p3 >= 2) by (apply prime_ge_2; auto).
  assert (p1 * p2 >= 4) by nia.
  assert (p1 * p2 * p3 >= 8) by nia.
  assert (p1 <= 21) by nia.
  assert (p2 <= 10) by nia.
  assert (p3 <= 5) by nia.
  assert (p1 * p2 <= 10) by nia.
  assert (p1 <= 5) by nia.
  assert (p1 = 2 \/ p1 = 3 \/ p1 = 4 \/ p1 = 5) by lia.
  assert (p2 = 2 \/ p2 = 3 \/ p2 = 4 \/ p2 = 5) by lia.
  assert (p3 = 2 \/ p3 = 3 \/ p3 = 4 \/ p3 = 5) by lia.
  destruct Hp1 as [Hp1gt Hp1div].
  destruct Hp2 as [Hp2gt Hp2div].
  destruct Hp3 as [Hp3gt Hp3div].
  assert (H4p1: p1 <> 4). {
    intro Heq4. subst p1. specialize (Hp1div 2). simpl in Hp1div. lia.
  }
  assert (H4p2: p2 <> 4). {
    intro Heq4. subst p2. specialize (Hp2div 2). simpl in Hp2div. lia.
  }
  assert (H4p3: p3 <> 4). {
    intro Heq4. subst p3. specialize (Hp3div 2). simpl in Hp3div. lia.
  }
  lia.
Qed.

Example test_is_multiply_prime_21 : is_multiply_prime_spec 21 false.
Proof.
  unfold is_multiply_prime_spec.
  split.
  - split.
    + intros H. discriminate H.
    + intros [Hgt [p1 [p2 [p3 [Hp1 [Hp2 [Hp3 Heq]]]]]]].
      exfalso.
      apply no_three_prime_factorization_21.
      exists p1, p2, p3. auto.
  - split.
    + intros _.
      right.
      apply no_three_prime_factorization_21.
    + intros _. reflexivity.
Qed.