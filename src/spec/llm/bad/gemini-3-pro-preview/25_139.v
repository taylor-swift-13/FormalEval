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

Fixpoint check_range (n start len : nat) : bool :=
  match len with
  | 0 => true
  | S len' => 
    if (n mod start =? 0) then false 
    else check_range n (S start) len'
  end.

Lemma check_range_correct : forall n start len,
  check_range n start len = true ->
  forall d, start <= d < start + len -> ~ Nat.divide d n.
Proof.
  induction len as [| len' IH]; intros.
  - lia.
  - simpl in H.
    destruct (n mod start =? 0) eqn:Heq.
    + discriminate.
    + apply Nat.eqb_neq in Heq.
      assert (Hnodiv: ~ Nat.divide start n).
      { intros Hdiv. apply Nat.mod_divide in Hdiv; try lia. congruence. }
      intros d0 Hd0.
      destruct (Nat.eq_dec d0 start).
      * subst. assumption.
      * apply IH; auto. lia.
Qed.

Lemma prime_check_ok : forall p,
  p > 1 ->
  check_range p 2 (p - 2) = true ->
  is_prime p.
Proof.
  intros p Hp Hcheck.
  split; auto.
  intros d Hdiv.
  destruct (Nat.eq_dec d 1); auto.
  destruct (Nat.eq_dec d p); auto.
  apply Nat.divide_pos_le in Hdiv; try lia.
  destruct d.
  - destruct Hdiv. rewrite Nat.mul_0_r in H. subst. lia.
  - destruct d.
    + contradiction.
    + assert (Hrange: 2 <= S (S d) < 2 + (p - 2)).
      { split; lia. }
      apply check_range_correct with (d:=S (S d)) in Hcheck; auto.
      contradiction.
Qed.

Example test_factorize_999988 : factorize_spec 999988 [2; 2; 11; 22727].
Proof.
  unfold factorize_spec.
  split.
  - vm_compute. reflexivity.
  - split.
    + repeat constructor.
      * apply prime_check_ok; [lia | vm_compute; reflexivity].
      * apply prime_check_ok; [lia | vm_compute; reflexivity].
      * apply prime_check_ok; [lia | vm_compute; reflexivity].
      * apply prime_check_ok; [lia | vm_compute; reflexivity].
    + repeat constructor; lia.
Qed.