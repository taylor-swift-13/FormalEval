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

Fixpoint no_divisors (d limit n fuel : nat) : bool :=
  match fuel with
  | 0 => false
  | S f => 
    if limit <? d then true
    else 
      if (n mod d) =? 0 then false
      else no_divisors (S d) limit n f
  end.

Lemma no_divisors_sound : forall fuel d limit n,
  limit < d + fuel ->
  d > 0 ->
  no_divisors d limit n fuel = true ->
  forall k, d <= k <= limit -> ~ Nat.divide k n.
Proof.
  induction fuel; intros.
  - simpl in H1. discriminate.
  - simpl in H1. destruct (limit <? d) eqn:E.
    + apply Nat.ltb_lt in E. lia.
    + destruct (n mod d =? 0) eqn:Div.
      * discriminate.
      * apply Nat.eqb_neq in Div.
        intros k Hk. destruct (Nat.eq_dec k d).
        -- subst. intro Hdiv. apply Nat.mod_divide in Hdiv; auto.
        -- apply IHfuel; auto.
           ++ apply Nat.ltb_ge in E. lia.
           ++ lia.
           ++ split; try lia.
Qed.

Lemma prime_check_correct : forall n,
  1 < n ->
  no_divisors 2 (pred n) n n = true ->
  is_prime n.
Proof.
  intros n Hgt Hcheck.
  split; auto.
  intros d Hdiv.
  destruct (le_lt_dec d 1).
  - destruct d; try lia. left. auto.
  - destruct (le_lt_dec n d).
    + apply Nat.divide_pos_le in Hdiv; try lia. right. lia.
    + exfalso.
      assert (2 <= d <= pred n) by lia.
      eapply no_divisors_sound in Hcheck; eauto.
      * lia.
      * lia.
Qed.

Example test_factorize_987654322 : factorize_spec 987654322 [2; 701; 704461].
Proof.
  unfold factorize_spec.
  split.
  - vm_compute. reflexivity.
  - split.
    + constructor.
      * apply prime_check_correct; try lia.
        vm_compute. reflexivity.
      * constructor.
        -- apply prime_check_correct; try lia.
           vm_compute. reflexivity.
        -- constructor.
           ++ apply prime_check_correct; try lia.
              vm_compute. reflexivity.
           ++ constructor.
    + repeat constructor.
Qed.