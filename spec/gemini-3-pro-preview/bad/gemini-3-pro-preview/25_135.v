Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Import ListNotations.
Open Scope nat_scope.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

Lemma nat_divide_Z_divide : forall a b, Nat.divide a b <-> Z.divide (Z.of_nat a) (Z.of_nat b).
Proof.
  split; intros [k H]; exists (Z.of_nat k).
  - rewrite H. apply Nat2Z.inj_mul.
  - apply Nat2Z.inj. rewrite Nat2Z.inj_mul. rewrite <- H.
    symmetry. apply Z2Nat.id. apply Z.mul_nonneg_nonneg; apply Nat2Z.is_nonneg.
Qed.

Lemma Z_prime_implies_nat_prime : forall n, prime (Z.of_nat n) -> is_prime n.
Proof.
  intros n Hp.
  split.
  + apply prime_ge_2 in Hp. lia.
  + intros d Hdiv.
    apply nat_divide_Z_divide in Hdiv.
    apply prime_divisors in Hdiv; [|assumption].
    destruct Hdiv as [E1 | [E2 | [E3 | E4]]].
    * left. apply Nat2Z.inj. rewrite E1. reflexivity.
    * right. inversion E2.
    * right. apply Nat2Z.inj. assumption.
    * right. inversion E4.
Qed.

Ltac check_prime_Z p :=
  let H := fresh in
  pose proof (prime_dec p) as H;
  vm_compute in H;
  destruct H as [H|H]; [ exact H | fail "Not a prime" ].

Example test_factorize_999986 : factorize_spec 999986 [2; 13; 38461].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + constructor.
      * apply Z_prime_implies_nat_prime. check_prime_Z 2%Z.
      * constructor.
        -- apply Z_prime_implies_nat_prime. check_prime_Z 13%Z.
        -- constructor.
           ++ apply Z_prime_implies_nat_prime. check_prime_Z 38461%Z.
           ++ constructor.
    + repeat constructor.
Qed.