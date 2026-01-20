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

Lemma is_prime_2 : is_prime 2.
Proof.
  unfold is_prime.
  split.
  - lia.
  - intros d Hd. lia.
Qed.

Example test_is_multiply_prime_8 : is_multiply_prime_spec 8 true.
Proof.
  unfold is_multiply_prime_spec.
  split.
  - split.
    + intros _.
      split.
      * lia.
      * exists 2, 2, 2.
        repeat split; try apply is_prime_2.
        reflexivity.
    + intros _. reflexivity.
  - split.
    + intros H. discriminate H.
    + intros [Hle | Hnot].
      * lia.
      * exfalso. apply Hnot.
        exists 2, 2, 2.
        repeat split; try apply is_prime_2.
        reflexivity.
Qed.