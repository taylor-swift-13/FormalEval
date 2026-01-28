Existing Coq output file content specification for the first test case `input = [2%Z], output = [2%Z]`:
```coq
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

Fixpoint check_prime_range (p d fuel : nat) : bool :=
  match fuel with
  | 0 => true
  | S f =>
    if p <? d * d then true
    else if p mod d =? 0 then false
    else check_prime_range p (S d) f
  end.

Lemma check_prime_range_sound : forall fuel p d,
  check_prime_range p d fuel = true ->
  forall k, d <= k -> k < d + fuel -> k * k <= p -> ~ Nat.divide k p.
Proof.
  induction fuel; intros p d Hcheck k Hdk Hkfuel Hsq Hdiv.
  - lia.
  - simpl in Hcheck.
    destruct (p <? d * d) eqn:Hlim.
    + apply Nat.ltb_lt in Hlim.
      assert (d * d <= k * k) by (apply Nat.mul_le_mono; lia).
      lia.
    + destruct (p mod d =? 0) eqn:Hmod.
      * discriminate.
      * apply Nat.eqb_neq in Hmod.
        assert (k = d \/ k > d) as [Heq | Hgt] by lia.
        -- subst. apply Nat.mod_divide in Hdiv; try lia. congruence.
        -- apply (IHfuel p (S d) Hcheck k); try lia.
Qed.

Lemma prime_sqrt : forall p,
  p > 1 ->
  (forall d, 2 <= d -> d * d <= p -> ~ Nat.divide d p) ->
  is_prime p.
Proof.
  intros p Hp Hchk.
  split; auto.
  intros d Hd.
  destruct (le_gt_dec d 1).
  - destruct d; [destruct Hd; discriminate | left; auto].
  - right.
    destruct (le_lt_dec d p); [|apply Nat.divide_pos_le in Hd; lia].
    destruct (eq_nat_dec d p); auto.
    apply Nat.mod_divide in Hd; try lia.
    assert (Hdecomp: p = d * (p / d)).
    { rewrite (Nat.div_mod p d) at 1; try lia. rewrite Hd. lia. }
    set (q := p / d) in *.
    assert (Hq_pos: q > 0).
    { destruct q; simpl in *; try lia. rewrite Nat.mul_0_r in Hdecomp. lia. }
    assert (q > 1).
    { destruct q; try lia. destruct q; try lia. rewrite Nat.mul_1_r in Hdecomp. subst. contradiction. }
    assert (Hq_div: Nat.divide q p).
    { exists d. rewrite Nat.mul_comm. auto. }
    assert (H_le: d * d <= p \/ q * q <= p).
    {
      destruct (le_lt_dec d q).
      - left. rewrite Hdecomp at 2. apply Nat.mul_le_mono_l; auto.
      - right. rewrite Hdecomp at 2. rewrite Nat.mul_comm. apply Nat.mul_le_mono_l; lia.
    }
    destruct H_le.
    + apply Nat.mod_divide in Hd; try lia.
      apply Hchk in H; try lia. congruence.
    + apply Nat.mod_divide in Hq_div; try lia.
      apply Hchk in H0; try lia. congruence.
Qed.

Lemma is_prime_via_check : forall p,
  p > 1 ->
  check_prime_range p 2 p = true ->
  is_prime p.
Proof.
  intros p Hp Hcheck.
  apply prime_sqrt; auto.
  intros d Hge Hsq.
  apply (check_prime_range_sound p p 2 Hcheck d); try lia.
Qed.

Example test_factorize_999982 : factorize_spec 999982 [2; 79; 6329].
Proof.
  unfold factorize_spec.
  split.
  - vm_compute. reflexivity.
  - split.
    + constructor.
      * apply is_prime_via_check; [lia | vm_compute; reflexivity].
      * constructor.
        -- apply is_prime_via_check; [lia | vm_compute; reflexivity].
        -- constructor.
           ++ apply is_prime_via_check; [lia | vm_compute; reflexivity].
           ++ constructor.
    + repeat constructor.
Qed.