Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

Fixpoint no_divisors (d n : nat) : bool :=
  match d with
  | S (S k) => if n mod d =? 0 then false else no_divisors (S k) n
  | _ => true
  end.

Lemma no_divisors_ok : forall d n,
  no_divisors d n = true ->
  forall k, 1 < k <= d -> ~ Nat.divide k n.
Proof.
  induction d as [|d IH]; intros n Hres k Hk Hdiv.
  - lia.
  - simpl in Hres.
    destruct d as [|d'].
    + lia.
    + destruct (n mod S (S d') =? 0) eqn:Hmod.
      * discriminate.
      * apply Nat.eqb_neq in Hmod.
        assert (k = S (S d') \/ k <= S d') by lia.
        destruct H as [Heq | Hle].
        -- subst k. apply Nat.mod_divide in Hdiv; [|lia]. congruence.
        -- apply IH; auto. lia.
Qed.

Lemma prove_prime : forall p,
  1 < p ->
  no_divisors (pred p) p = true ->
  is_prime p.
Proof.
  intros p Hp Hcheck. split; auto.
  intros d Hdiv.
  destruct (le_lt_dec d 1).
  - destruct d; [|destruct d]; try lia.
    destruct Hdiv as [x Hx]. rewrite Nat.mul_0_r in Hx. subst p. lia.
    left. reflexivity.
  - destruct (Nat.eq_dec d p).
    + right. assumption.
    + exfalso.
      apply Nat.divide_pos_le in Hdiv; [|lia].
      assert (1 < d <= pred p) by lia.
      eapply no_divisors_ok in Hcheck; eauto.
Qed.

Example test_factorize_999984 : factorize_spec 999984 [2; 2; 2; 2; 3; 83; 251].
Proof.
  unfold factorize_spec.
  split.
  - vm_compute. reflexivity.
  - split.
    + repeat constructor.
      all: apply prove_prime; [lia | vm_compute; reflexivity].
    + repeat constructor; lia.
Qed.