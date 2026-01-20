Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (p : Z) : Prop :=
  p > 1 /\ forall d : Z, 0 < d -> Z.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : Z) (factors : list Z) : Prop :=
  fold_right Z.mul 1 factors = n /\
  Forall is_prime factors /\
  Sorted Z.le factors.

Fixpoint no_divisors (n : Z) (d : Z) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S f =>
    if (d * d >? n)%Z then true
    else if (n mod d =? 0)%Z then false
    else no_divisors n (d + 1) f
  end.

Definition is_prime_check (n : Z) : bool :=
  if (n <=? 1)%Z then false
  else no_divisors n 2 (Z.to_nat (Z.sqrt n) + 2).

Lemma no_divisors_correct : forall n d fuel,
  (1 < n)%Z -> (1 < d)%Z ->
  no_divisors n d fuel = true ->
  forall k, (d <= k)%Z -> (k * k <= n)%Z -> ~ Z.divide k n.
Proof.
  intros n d fuel Hn Hd Hcheck k Hdk Hkn Hdiv.
  revert d Hd Hcheck Hdk.
  induction fuel; intros d Hd Hcheck Hdk.
  - simpl in Hcheck. discriminate.
  - simpl in Hcheck.
    destruct (d * d >? n)%Z eqn:Hsq.
    + apply Z.gtb_lt in Hsq. lia.
    + destruct (n mod d =? 0)%Z eqn:Hrem.
      * discriminate.
      * apply Z.eqb_neq in Hrem.
        assert (k = d \/ k >= d + 1)%Z by lia.
        destruct H as [Heq | Hgt].
        -- subst k. apply Z.mod_divide in Hdiv; try lia. contradiction.
        -- apply IHfuel with (d := d + 1); try lia.
           assumption.
Qed.

Lemma is_prime_check_correct : forall n, is_prime_check n = true -> is_prime n.
Proof.
  intros n Hcheck.
  unfold is_prime_check in Hcheck.
  destruct (n <=? 1)%Z eqn:Hle.
  - discriminate.
  - apply Z.leb_nle in Hle.
    split; [lia|].
    intros d Hpos Hdiv.
    destruct (Z.le_gt_cases d 1) as [Hsmall | Hlarge].
    + assert (d = 1) by lia. left. assumption.
    + destruct (Z.le_gt_cases d n) as [Hrange | Hbig].
      * destruct (Z.eq_dec d n); [right; assumption|].
        destruct (Z.le_gt_cases (d * d) n).
        -- exfalso.
           apply (no_divisors_correct n 2 (Z.to_nat (Z.sqrt n) + 2)); try lia.
           assumption. assumption. assumption. assumption.
        -- set (q := n / d).
           assert (Hqn: n = q * d). { apply Z.divide_pos_div; lia. }
           assert (Hqdiv: Z.divide q n). { exists d. rewrite Z.mul_comm. assumption. }
           assert (Hqsmall: q * q < n). {
             apply Z.square_lt_simpl_nonneg with (n:=d); try lia.
             rewrite <- Hqn.
             assert (q < d). {
                apply Z.square_gt_simpl_nonneg with (n:=n); try lia.
                rewrite Hqn. 
                assert (d * d > q * d). { rewrite <- Hqn. assumption. }
                apply Z.mul_lt_mono_pos_r in H; try lia.
             }
             transitivity (q * d); [|rewrite <- Hqn; lia].
             apply Z.mul_lt_mono_pos_l; lia.
           }
           exfalso.
           apply (no_divisors_correct n 2 (Z.to_nat (Z.sqrt n) + 2)); try lia.
           assumption. lia. lia. assumption.
      * apply Z.divide_pos_le in Hdiv; lia.
Qed.

Example test_factorize_987654323 : factorize_spec 987654323 [987654323].
Proof.
  split.
  - reflexivity.
  - split.
    + constructor.
      * apply is_prime_check_correct. vm_compute. reflexivity.
      * constructor.
    + constructor.
Qed.