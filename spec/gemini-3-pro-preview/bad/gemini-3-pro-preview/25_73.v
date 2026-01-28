Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

Module PrimeCheck.
  Open Scope Z_scope.

  Definition is_prime_Z (p : Z) : Prop :=
    p > 1 /\ forall d : Z, 1 < d < p -> ~ (d | p).

  Lemma nat_Z_prime_equiv : forall n : nat,
    is_prime_Z (Z.of_nat n) -> is_prime n.
  Proof.
    intros n [Hgt Hnodiv].
    split.
    - apply Nat2Z.inj_lt. simpl. apply Hgt.
    - intros d Hdiv.
      destruct (Nat.eq_dec d 1); [left; auto|].
      destruct (Nat.eq_dec d n); [right; auto|].
      exfalso.
      apply Nat2Z.inj_divide in Hdiv.
      assert (1 < Z.of_nat d < Z.of_nat n). {
        split.
        - apply Nat2Z.inj_lt. destruct d; try lia.
          destruct d; try lia.
        - apply Nat2Z.inj_lt. apply Nat.divide_pos_le in Hdiv; try lia.
          assert (d <> n) by auto.
          assert (d <= n)%nat by (apply Nat.divide_pos_le; lia).
          lia.
      }
      eapply Hnodiv; eassumption.
  Qed.

  Fixpoint check_range (n : Z) (d : Z) (fuel : nat) : bool :=
    match fuel with
    | O => false
    | S f => 
      if d * d >? n then true
      else if Z.rem n d =? 0 then false
      else check_range n (d + 1) f
    end.

  Lemma check_range_sound : forall fuel n d,
    (2 <= d) ->
    check_range n d fuel = true ->
    (forall k, d <= k -> k * k <= n -> ~ (k | n)).
  Proof.
    induction fuel; intros n d Hle Hcheck k Hk1 Hk2 Hdiv.
    - simpl in Hcheck. discriminate.
    - simpl in Hcheck.
      destruct (d * d >? n) eqn:Hsq.
      + apply Z.gt_lt in Hsq.
        assert (k * k > n). {
           apply Z.lt_le_trans with (m := d*d); try assumption.
           apply Z.mul_le_mono_nonneg; lia.
        }
        lia.
      + destruct (n mod d =? 0) eqn:Hrem.
        * discriminate.
        * apply Z.eqb_neq in Hrem.
          apply Z.rem_divide in Hdiv; try lia.
          assert (k = d \/ k > d) by lia.
          destruct H as [Heq | Hgt].
          -- subst. contradiction.
          -- eapply IHfuel; try eassumption.
             lia.
  Qed.

  Lemma check_prime_Z_correct : forall n fuel,
    (1 < n) ->
    check_range n 2 fuel = true ->
    is_prime_Z n.
  Proof.
    intros n fuel Hgt Hcheck.
    split; try assumption.
    intros d Hrange Hdiv.
    destruct (Z.le_gt_cases (d*d) n).
    - eapply check_range_sound; try eassumption; try lia.
    - assert (Hq: exists q, n = q * d). { exists (n/d). apply Z.divide_div_mul_exact; try lia. apply Hdiv. }
      destruct Hq as [q Hq].
      assert (Hqdiv: (q | n)). { exists d. rewrite Z.mul_comm. assumption. }
      assert (Hqn: q * d = n) by assumption.
      assert (Hdpos: 0 < d) by lia.
      assert (Hqpos: 0 < q). { apply Z.mul_pos_pos_rev with (b:=d); lia. }
      assert (d > q). {
        apply Z.mul_lt_mono_pos_r with (p:=d); try lia.
        rewrite Hqn.
        lia.
      }
      assert (1 < q). {
        apply Z.nle_gt. intro Hle.
        assert (q = 1) by lia. subst.
        lia.
      }
      assert (q * q < n). {
        rewrite <- Hqn.
        apply Z.mul_lt_mono_pos_l; try lia.
      }
      eapply check_range_sound with (d:=2) (fuel:=fuel); try eassumption; try lia.
      + lia.
      + apply Z.lt_le_incl. assumption.
  Qed.
End PrimeCheck.

Example test_factorize_3 : factorize_spec 2147483645 [5; 19; 22605091].
Proof.
  unfold factorize_spec.
  split.
  - (* Product check *)
    cbn [fold_right]. lia.
  - split.
    + (* Primality check *)
      repeat constructor.
      * (* 5 *)
        apply PrimeCheck.nat_Z_prime_equiv.
        apply PrimeCheck.check_prime_Z_correct with (fuel:=5%nat).
        -- lia.
        -- vm_compute. reflexivity.
      * (* 19 *)
        apply PrimeCheck.nat_Z_prime_equiv.
        apply PrimeCheck.check_prime_Z_correct with (fuel:=10%nat).
        -- lia.
        -- vm_compute. reflexivity.
      * (* 22605091 *)
        apply PrimeCheck.nat_Z_prime_equiv.
        apply PrimeCheck.check_prime_Z_correct with (fuel:=5000%nat).
        -- lia.
        -- vm_compute. reflexivity.
    + (* Sorted check *)
      repeat constructor; lia.
Qed.