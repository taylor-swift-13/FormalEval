Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

Open Scope Z_scope.

Definition problem_59_pre (n : Z) : Prop := (Z.gt n 1 /\ ~ (prime n)).

Definition problem_59_spec (n p: Z) : Prop :=
  (
    prime p /\ (p | n) /\
    (forall q: Z, (prime q /\ (q | n)) -> Z.le q p)
  ).

(* Lemma: 2 is prime - use the library *)
Lemma prime_2 : prime 2.
Proof.
  exact prime_2.
Qed.

(* Lemma: 3 is prime - use the library *)
Lemma prime_3 : prime 3.
Proof.
  exact prime_3.
Qed.

(* Helper to show 5 is prime *)
Lemma prime_5 : prime 5.
Proof.
  apply prime_intro.
  - lia.
  - intros n Hn Hdiv.
    destruct Hn as [Hn1 Hn2].
    destruct Hdiv as [k Hk].
    assert (n > 0) by lia.
    assert (k > 0) by nia.
    assert (n <= 5) by nia.
    assert (n = 2 \/ n = 3 \/ n = 4 \/ n = 5) by lia.
    destruct H2 as [Hn_eq | [Hn_eq | [Hn_eq | Hn_eq]]].
    + subst n. assert (5 = 2 * k) by lia. lia.
    + subst n. assert (5 = 3 * k) by lia. lia.
    + subst n. assert (5 = 4 * k) by lia. lia.
    + right. lia.
Qed.

(* 5 divides 15 *)
Lemma div_5_15 : (5 | 15).
Proof.
  exists 3. reflexivity.
Qed.

(* 15 is not prime *)
Lemma not_prime_15 : ~ prime 15.
Proof.
  intro H.
  assert (Hrel : rel_prime 15 3 \/ 3 = 15).
  { 
    apply H.
    - lia.
    - exists 5. reflexivity.
  }
  destruct Hrel as [Hrel | Hrel].
  - assert (Hgcd : Z.gcd 15 3 = 3).
    { reflexivity. }
    unfold rel_prime in Hrel.
    rewrite Hgcd in Hrel.
    lia.
  - lia.
Qed.

(* Main lemma: any prime factor of 15 is at most 5 *)
Lemma prime_factor_15_le_5 : forall q, prime q -> (q | 15) -> q <= 5.
Proof.
  intros q Hprime Hdiv.
  destruct Hdiv as [k Hk].
  assert (Hq_pos : q >= 2).
  { destruct Hprime. lia. }
  assert (k > 0) by nia.
  assert (q <= 15) by nia.
  (* q divides 15 = 3 * 5, so q is 3 or 5 *)
  assert (q = 2 \/ q = 3 \/ q = 4 \/ q = 5 \/ q >= 6) by lia.
  destruct H1 as [Hq | [Hq | [Hq | [Hq | Hq]]]].
  - (* q = 2: but 2 does not divide 15 *)
    subst q. lia.
  - (* q = 3 *) lia.
  - (* q = 4: not prime *)
    subst q.
    exfalso.
    destruct Hprime as [_ Hprime_rel].
    assert (Hrel : rel_prime 4 2 \/ 2 = 4).
    { apply Hprime_rel. lia. exists 2. reflexivity. }
    destruct Hrel as [Hrel | Hrel].
    + unfold rel_prime in Hrel.
      assert (Z.gcd 4 2 = 2) by reflexivity.
      lia.
    + lia.
  - (* q = 5 *) lia.
  - (* q >= 6 *)
    assert (q * 1 <= q * k) by nia.
    assert (q <= 15) by lia.
    assert (q = 6 \/ q = 7 \/ q = 8 \/ q = 9 \/ q = 10 \/ q = 11 \/ q = 12 \/ q = 13 \/ q = 14 \/ q = 15) by lia.
    destruct H3 as [Hq6 | [Hq7 | [Hq8 | [Hq9 | [Hq10 | [Hq11 | [Hq12 | [Hq13 | [Hq14 | Hq15]]]]]]]]].
    all: subst q; try lia.
    (* q = 15: 15 is not prime *)
    exfalso. apply not_prime_15. assumption.
Qed.

Example test_largest_prime_factor_15 :
  problem_59_pre 15 /\ problem_59_spec 15 5.
Proof.
  split.
  - unfold problem_59_pre.
    split.
    + lia.
    + exact not_prime_15.
  - unfold problem_59_spec.
    split.
    + exact prime_5.
    + split.
      * exact div_5_15.
      * intros q [Hprime Hdiv].
        apply prime_factor_15_le_5; assumption.
Qed.