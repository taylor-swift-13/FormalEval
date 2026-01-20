Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

Lemma is_prime_via_Z : forall n, 
  (1 < n)%nat -> 
  prime (Z.of_nat n) -> 
  is_prime n.
Proof.
  intros n Hn Hprime.
  split; [assumption|].
  intros d Hd.
  apply Nat2Z.inj_divide in Hd.
  assert (Hd_ge_0: (0 <= Z.of_nat d)%Z) by apply Nat2Z.is_nonneg.
  assert (Hn_ge_0: (0 <= Z.of_nat n)%Z) by apply Nat2Z.is_nonneg.
  destruct (Z.eq_dec (Z.of_nat d) 1) as [H1|Hnot1].
  { left. apply Nat2Z.inj. assumption. }
  destruct (Z.eq_dec (Z.of_nat d) (Z.of_nat n)) as [Hn_eq|Hnotn].
  { right. apply Nat2Z.inj. assumption. }
  exfalso.
  assert (Hle: (Z.of_nat d <= Z.of_nat n)%Z).
  { apply Z.divide_pos_le; [lia|assumption]. }
  assert (Hge1: (1 <= Z.of_nat d)%Z).
  { destruct (Z.of_nat d) eqn:Ed; try lia.
    assert (Z.of_nat d = 0)%Z by lia.
    rewrite H in Hd. apply Z.divide_0_l in Hd. subst.
    lia.
  }
  assert (Hrange: (1 < Z.of_nat d < Z.of_nat n)%Z) by lia.
  destruct Hprime as [_ Hrel].
  specialize (Hrel (Z.of_nat d) Hrange).
  assert (Hgcd: Z.gcd (Z.of_nat d) (Z.of_nat n) = Z.of_nat d).
  { apply Z.gcd_divide_l; [lia|assumption]. }
  rewrite Hgcd in Hrel.
  lia.
Qed.

Example test_factorize_large : factorize_spec 123456785 [5; 24691357].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    apply Nat2Z.inj.
    simpl.
    rewrite Nat2Z.inj_mul.
    rewrite Nat2Z.inj_mul.
    vm_compute.
    reflexivity.
  - split.
    + (* Part 2: Primality check *)
      constructor.
      * (* is_prime 5 *)
        apply is_prime_via_Z; [lia|].
        generalize (prime_dec (Z.of_nat 5)); intro Hp.
        vm_compute in Hp.
        destruct Hp; [assumption|discriminate].
      * constructor.
        -- (* is_prime 24691357 *)
           apply is_prime_via_Z; [lia|].
           generalize (prime_dec (Z.of_nat 24691357)); intro Hp.
           vm_compute in Hp.
           destruct Hp; [assumption|discriminate].
        -- constructor.
    + (* Part 3: Sorted check *)
      repeat constructor.
      lia.
Qed.