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

Lemma prime_2 : is_prime 2.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd. lia.
Qed.

Lemma prime_3 : is_prime 3.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd.
    assert (d = 2) by lia.
    subst. compute. discriminate.
Qed.

Lemma prime_5 : is_prime 5.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd.
    assert (d = 2 \/ d = 3 \/ d = 4) by lia.
    destruct H as [H | [H | H]]; subst; compute; discriminate.
Qed.

Example test_is_multiply_prime_30 : is_multiply_prime_spec 30 true.
Proof.
  unfold is_multiply_prime_spec.
  split.
  - split.
    + intros _.
      split.
      * lia.
      * exists 2, 3, 5.
        split. exact prime_2.
        split. exact prime_3.
        split. exact prime_5.
        reflexivity.
    + intros _. reflexivity.
  - split.
    + intros H. discriminate H.
    + intros [H | H].
      * lia.
      * exfalso. apply H.
        exists 2, 3, 5.
        split. exact prime_2.
        split. exact prime_3.
        split. exact prime_5.
        reflexivity.
Qed.