Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition problem_59_pre (n : Z) : Prop := (Z.gt n 1 /\ ~ (prime n)).

Definition problem_59_spec (n p: Z) : Prop :=
  prime p /\ (p | n) /\ (forall q: Z, (prime q /\ (q | n)) -> q <= p).

(* Helper lemmas about prime 3 and prime 5 *)

Lemma prime_3 : prime 3.
Proof.
  apply prime_prime; lia.
  unfold prime.
  split; [lia |].
  intros d [_ Hd].
  destruct (Z.eq_dec d 1).
  - right; assumption.
  - destruct (Z.eq_dec d 3).
    + left; assumption.
    + exfalso; lia.
Qed.

Lemma prime_5 : prime 5.
Proof.
  apply prime_prime; lia.
  unfold prime.
  split; [lia |].
  intros d [_ Hd].
  destruct (Z.eq_dec d 1).
  - right; assumption.
  - destruct (Z.eq_dec d 5).
    + left; assumption.
    + exfalso; lia.
Qed.

(* If a prime divides a product, it divides one of the factors *)
Lemma prime_divide_mult_nontrivial:
  forall q a b : Z, prime q -> q | a * b -> q | a \/ q | b.
Proof.
  intros.
  apply prime_divide_mult; assumption.
Qed.

(* If prime p divides prime q, and both prime, then p = q *)
Lemma prime_divide_prime_unique:
  forall p q : Z, prime p -> p | q -> prime q -> p = q.
Proof.
  intros p q Hp Hpdiv Hq.
  destruct (Z.eq_dec p q).
  - assumption.
  - exfalso.
    unfold prime in Hp, Hq.
    destruct Hp as [_ Hpdivs].
    destruct Hq as [_ Hqdivs].
    specialize (Hpdivs p Hpdiv).
    destruct Hpdivs as [Hp1 | Hpq].
    + subst p.
      lia.
    + lia.
Qed.

Example problem_59_test_15:
  problem_59_pre 15 /\ problem_59_spec 15 5.
Proof.
  split.
  - (* prove precondition *)
    unfold problem_59_pre.
    split.
    + lia.
    + unfold not.
      intros Hprim.
      (* 15 is composite, so cannot be prime *)
      (* use prime definition *)
      unfold prime in Hprim.
      destruct Hprim as [_ Hdiv].
      specialize (Hdiv 3).
      assert (H: 3 | 15) by lia.
      specialize (Hdiv H).
      destruct Hdiv as [H3 | H15].
      * lia.
      * lia.
  - (* prove specification *)
    unfold problem_59_spec.
    split.
    + apply prime_5.
    + split.
      * exists 3. lia.
      * intros q [Hqprime Hqdiv].
        (* prime factors of 15 are 3 and 5 *)
        destruct (Z.eq_dec q 3) as [Heq3|Hneq3].
        { subst; lia. }
        destruct (Z.eq_dec q 5) as [Heq5|Hneq5].
        { subst; lia. }
        (* Else q divides 15, prime, but q ≠ 3,5 *)
        assert (Hmult := prime_divide_mult_nontrivial q 3 5 Hqprime Hqdiv).
        destruct Hmult as [Hq3 | Hq5].
        - apply (prime_divide_prime_unique q 3 Hqprime Hq3 prime_3); lia.
        - apply (prime_divide_prime_unique q 5 Hqprime Hq5 prime_5); lia.
Qed.