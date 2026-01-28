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

Fixpoint check_range (d : nat) (count : nat) (n : nat) : bool :=
  match count with
  | 0 => true
  | S c => if (n mod d =? 0) then false else check_range (S d) c n
  end.

Lemma check_range_correct : forall count d n,
  d > 0 ->
  check_range d count n = true ->
  forall k, d <= k < d + count -> ~ Nat.divide k n.
Proof.
  induction count; intros d n Hdpos Hcheck k Hk Hdiv.
  - lia.
  - simpl in Hcheck.
    destruct (n mod d =? 0) eqn:Hrem; try discriminate.
    destruct (Nat.eq_dec k d).
    + subst. apply Nat.eqb_neq in Hrem.
      apply Nat.mod_divide in Hdiv; auto.
      lia.
    + apply IHcount with (k:=k) in Hcheck; auto.
      lia. lia.
Qed.

Lemma prime_test_sqrt : forall n limit,
  n > 1 ->
  limit * limit > n ->
  check_range 2 limit n = true ->
  is_prime n.
Proof.
  intros n limit Hn Hsq Hcheck.
  split; auto.
  intros d Hdiv.
  destruct (le_lt_dec d 1) as [Hle|Hgt].
  { destruct d; [|destruct d]; try lia.
    destruct Hdiv as [x Hx]. rewrite Nat.mul_0_r in Hx. subst. lia.
    left. lia. }
  right.
  destruct (le_lt_dec d limit).
  - assert (2 <= d < 2 + limit).
    { split; lia. }
    apply check_range_correct with (k:=d) in Hcheck; auto. 2: lia.
    contradiction.
  - destruct Hdiv as [q Hq].
    destruct (le_lt_dec q 1).
    { destruct q; try lia.
      - rewrite Nat.mul_0_l in Hq. subst. lia.
      - rewrite Nat.mul_1_l in Hq. subst. reflexivity. }
    destruct (le_lt_dec q limit).
    {
      assert (2 <= q < 2 + limit) by lia.
      apply check_range_correct with (k:=q) in Hcheck; auto. 2: lia.
      exists d. rewrite Nat.mul_comm. auto.
    }
    assert (d * q > n).
    {
      apply Nat.lt_le_trans with (m := limit * limit); auto.
      apply Nat.mul_lt_mono; lia.
    }
    rewrite Hq in H0. lia.
Qed.

Example test_factorize_1207945 : factorize_spec 1207945 [5; 241589].
Proof.
  unfold factorize_spec.
  split.
  - vm_compute. reflexivity.
  - split.
    + constructor.
      * apply prime_test_sqrt with (limit := 3); try lia.
        vm_compute. reflexivity.
      * constructor.
        -- apply prime_test_sqrt with (limit := 492); try lia.
           vm_compute. reflexivity.
        -- constructor.
    + repeat constructor.
Qed.