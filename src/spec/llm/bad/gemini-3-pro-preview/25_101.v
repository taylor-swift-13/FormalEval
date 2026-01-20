Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

Lemma Zprime_to_nat_prime : forall n, prime (Z.of_nat n) -> is_prime n.
Proof.
  intros n Hp. destruct Hp as [Hgt Hndiv].
  split.
  - apply Nat2Z.inj_lt. apply Hgt.
  - intros d Hd.
    apply Nat2Z.inj_divide in Hd.
    destruct (Z.eq_dec (Z.of_nat d) 1).
    + left. apply Nat2Z.inj. assumption.
    + right.
      destruct (Z.eq_dec (Z.of_nat d) (Z.of_nat n)).
      * apply Nat2Z.inj. assumption.
      * exfalso.
        apply (Hndiv (Z.of_nat d)).
        -- split.
           ++ apply Z.neq_sym in n0.
              destruct (Z.le_gt_cases 1 (Z.of_nat d)).
              ** destruct (Z.eq_dec 1 (Z.of_nat d)); try congruence. assumption.
              ** destruct d; try lia.
                 apply Z.divide_0_l in Hd. subst. lia.
           ++ apply Z.divide_pos_le in Hd; try lia.
              destruct (Z.eq_dec (Z.of_nat d) (Z.of_nat n)); try congruence.
              lia.
        -- assumption.
Qed.

Example test_factorize_large : factorize_spec 112234366 [2; 56117183].
Proof.
  unfold factorize_spec.
  split.
  - simpl fold_right. lia.
  - split.
    + constructor.
      * apply Zprime_to_nat_prime.
        apply prime_2.
      * constructor.
        -- apply Zprime_to_nat_prime.
           let p := fresh "p" in
           pose (p := prime_dec (Z.of_nat 56117183));
           vm_compute in p;
           destruct p; assumption.
        -- constructor.
    + repeat constructor.
Qed.