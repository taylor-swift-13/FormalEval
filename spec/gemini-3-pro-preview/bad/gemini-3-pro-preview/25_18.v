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

Lemma nat_prime_is_prime : forall p, PeanoNat.Nat.prime p -> is_prime p.
Proof.
  intros p [Hneq Hdiv].
  split.
  - destruct p.
    + specialize (Hdiv 2).
      assert (Nat.divide 2 0) by (exists 0; auto).
      apply Hdiv in H; destruct H; discriminate.
    + destruct p; [congruence | lia].
  - assumption.
Qed.

Lemma is_prime_via_Z : forall z, 
  (1 < z)%Z -> 
  Znumtheory.prime z -> 
  is_prime (Z.to_nat z).
Proof.
  intros z Hz Hp.
  apply nat_prime_is_prime.
  apply prime_Z_nat.
  assumption.
Qed.

Definition Zprime_bool (z : Z) : bool :=
  if Znumtheory.prime_dec z then true else false.

Lemma Zprime_bool_true : forall z, Zprime_bool z = true -> prime z.
Proof.
  intros z H. unfold Zprime_bool in H.
  destruct (prime_dec z); auto; discriminate.
Qed.

Example test_factorize_big : factorize_spec (Z.to_nat 987654321) (map Z.to_nat [3; 3; 17; 17; 379721]).
Proof.
  unfold factorize_spec.
  split.
  - rewrite !map_cons, map_nil.
    rewrite !fold_right_cons, fold_right_nil, Nat.mul_1_r.
    rewrite !Z2Nat.inj_mul; try lia.
    apply Z2Nat.inj_iff; try lia.
    vm_compute. reflexivity.
  - split.
    + rewrite !map_cons, map_nil.
      repeat constructor.
      all: apply is_prime_via_Z; [lia| apply Zprime_bool_true; vm_compute; reflexivity].
    + rewrite !map_cons, map_nil.
      repeat constructor.
      all: apply Z2Nat.inj_le; try lia; vm_compute; congruence.
Qed.