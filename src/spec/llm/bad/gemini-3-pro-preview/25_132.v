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

Lemma is_prime_correct : forall p, is_prime p <-> prime (Z.of_nat p).
Proof.
  intros p. split.
  - intros [Hgt Hdiv]. split.
    + apply Nat2Z.inj_lt. simpl. assumption.
    + intros d Hrange Hd_div.
      apply Nat2Z.inj_divide in Hd_div.
      destruct (Hdiv (Z.to_nat d) Hd_div) as [Heq1 | Heq2].
      * apply (f_equal Z.of_nat) in Heq1. rewrite Z2Nat.id in Heq1; try lia.
        subst. lia.
      * apply (f_equal Z.of_nat) in Heq2. rewrite Z2Nat.id in Heq2; try lia.
        subst. lia.
  - intros [Hgt Hdiv]. split.
    + apply Nat2Z.inj_lt in Hgt. simpl in Hgt. assumption.
    + intros d Hd_div.
      apply Nat2Z.inj_divide in Hd_div.
      destruct (le_lt_dec d 1).
      * destruct d; try lia. left. auto.
      * destruct (le_lt_dec d p).
        -- destruct (Nat.eq_dec d p).
           ++ right. auto.
           ++ exfalso. apply (Hdiv (Z.of_nat d)).
              ** split; apply Nat2Z.inj_lt; simpl; try lia; try assumption.
              ** assumption.
        -- apply Nat.divide_pos_le in Hd_div; try lia.
           apply Nat2Z.inj_le in Hd_div. lia.
Qed.

Ltac prove_prime :=
  apply is_prime_correct;
  match goal with
  | [ |- prime ?z ] =>
    let h := constr:(prime_dec z) in
    let h' := eval vm_compute in h in
    match h' with
    | left ?proof => exact proof
    end
  end.

Example test_factorize_1003000997 : factorize_spec (Z.to_nat 1003000997%Z) [23; 317; 137567].
Proof.
  unfold factorize_spec.
  split.
  - (* Product check *)
    apply Nat2Z.inj.
    rewrite Z2Nat.id; [|vm_compute; reflexivity].
    simpl.
    repeat rewrite Nat2Z.inj_mul.
    vm_compute. reflexivity.
  - split.
    + (* Primality check *)
      repeat constructor; try prove_prime.
    + (* Sorted check *)
      repeat constructor; simpl; try lia.
Qed.