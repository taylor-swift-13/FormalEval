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

(* Helper definitions for primality checking of large numbers *)
Fixpoint no_divisors (k n : nat) : bool :=
  match k with
  | 0 => true
  | 1 => true
  | S k' => if Nat.eqb (n mod (S k')) 0 then false else no_divisors k' n
  end.

Lemma no_divisors_correct : forall k n,
  no_divisors k n = true ->
  forall d, 1 < d <= k -> ~ Nat.divide d n.
Proof.
  induction k.
  - intros. lia.
  - intros n H d Hrange.
    simpl in H.
    destruct (Nat.eqb (n mod S k) 0) eqn:Heq.
    + discriminate.
    + destruct (Nat.eq_dec d (S k)).
      * subst. intro Hdiv. apply Nat.eqb_neq in Heq. apply Heq.
        apply Nat.mod_divide; [lia|assumption].
      * apply IHk; [assumption|lia|assumption].
Qed.

Lemma is_prime_check : forall n,
  n > 1 ->
  no_divisors (pred n) n = true ->
  is_prime n.
Proof.
  intros n Hgt Hcheck.
  split; [assumption|].
  intros d Hdiv.
  destruct (le_lt_dec d 1).
  - destruct d.
    + destruct Hdiv as [x Hx]. rewrite Nat.mul_0_r in Hx. discriminate.
    + left. lia.
  - right.
    destruct (Nat.eq_dec d n); [assumption|].
    apply Nat.divide_pos_le in Hdiv; [|lia].
    assert (d <= pred n) by lia.
    apply no_divisors_correct with (k := pred n) (d := d) in Hcheck; [|lia].
    exfalso. apply Hcheck; assumption.
Qed.

Example test_factorize_112234372 : factorize_spec 112234372 [2; 2; 28058593].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    vm_compute. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      constructor.
      * (* 2 *)
        apply is_prime_check; [lia | vm_compute; reflexivity].
      * constructor.
        -- (* 2 *)
           apply is_prime_check; [lia | vm_compute; reflexivity].
        -- constructor.
           ++ (* 28058593 *)
              apply is_prime_check; [lia | vm_compute; reflexivity].
           ++ constructor.
    + (* Part 3: Sorted check *)
      repeat constructor; lia.
Qed.