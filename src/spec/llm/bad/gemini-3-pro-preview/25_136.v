Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (p : Z) : Prop :=
  p > 1 /\ forall d : Z, Z.divide d p -> d = 1 \/ d = p \/ d = -1 \/ d = -p.

Definition factorize_spec (n : Z) (factors : list Z) : Prop :=
  fold_right Z.mul 1 factors = n /\
  Forall is_prime factors /\
  Sorted Z.le factors.

Fixpoint no_divisors (p : Z) (d : Z) (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S f => 
    if (Z.rem p d =? 0) then false else no_divisors p (d + 1) f
  end.

Lemma no_divisors_sound : forall p d fuel,
  no_divisors p d fuel = true ->
  forall x, d <= x < d + Z.of_nat fuel -> ~ Z.divide x p.
Proof.
  induction fuel; intros.
  - simpl in H0. lia.
  - simpl in H.
    destruct (Z.rem p d =? 0) eqn:Heq.
    + discriminate.
    + apply Z.eqb_neq in Heq.
      assert (x = d \/ d + 1 <= x < d + 1 + Z.of_nat fuel) by (simpl in H0; lia).
      destruct H1.
      * subst. intro Hdiv. apply Z.rem_divide in Hdiv; [|lia]. contradiction.
      * apply IHfuel; auto.
Qed.

Lemma check_prime_correct : forall p,
  1 < p ->
  no_divisors p 2 (Z.to_nat (p - 2)) = true ->
  is_prime p.
Proof.
  intros p Hlt Hchk.
  split; auto.
  intros d Hdiv.
  assert (d <> 0). { intro; subst. apply Z.divide_0_l in Hdiv. lia. }
  assert (Habs: Z.divide (Z.abs d) p). { apply Z.divide_abs_l. auto. }
  assert (Hbounds: 1 <= Z.abs d <= p).
  { split. 
    - apply Z.abs_pos; auto. 
    - apply Z.divide_pos_le; auto. apply Z.abs_nonneg. }
  destruct (Z.eq_dec (Z.abs d) 1).
  { apply Z.abs_eq_1_iff in e. destruct e; [left|right; right; right]; auto. }
  destruct (Z.eq_dec (Z.abs d) p).
  { apply Z.abs_eq_iff in e. destruct e; [right; left|right; right; left]; auto. }
  exfalso.
  assert (2 <= Z.abs d < p).
  { split. lia. lia. }
  apply (no_divisors_sound p 2 (Z.to_nat (p - 2)) Hchk (Z.abs d)).
  - rewrite Z2Nat.id; lia.
  - auto.
Qed.

Example test_factorize_987654327 : factorize_spec 987654327 [3; 11; 31; 163; 5923].
Proof.
  unfold factorize_spec.
  split.
  - vm_compute. reflexivity.
  - split.
    + repeat constructor; apply check_prime_correct; try lia; vm_compute; reflexivity.
    + repeat constructor; simpl; try lia.
Qed.