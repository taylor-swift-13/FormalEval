Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Fixpoint check_prime_aux (n : nat) (p : Z) : bool :=
  match n with
  | 0%nat => true
  | S k => (Z.gcd (Z.of_nat n) p =? 1) && check_prime_aux k p
  end.

Lemma check_prime_aux_correct : forall n p k,
  (1 <= k <= n)%nat ->
  check_prime_aux n p = true ->
  Z.gcd (Z.of_nat k) p = 1.
Proof.
  induction n; intros p k Hrange Hcheck.
  - lia.
  - simpl in Hcheck.
    apply andb_true_iff in Hcheck. destruct Hcheck as [H1 H2].
    destruct (Nat.eq_dec k (S n)).
    + subst. apply Z.eqb_eq in H1. exact H1.
    + apply IHn; try assumption. lia.
Qed.

Example test_is_prime_197 : is_prime_spec 197 true.
Proof.
  unfold is_prime_spec.
  split; [intro; clear H | intro; reflexivity].
  apply prime_intro.
  - lia.
  - intros n Hn.
    assert (Hcheck: check_prime_aux 196 197 = true) by (vm_compute; reflexivity).
    assert (Hrange: (1 <= Z.to_nat n <= 196)%nat).
    { split.
      - apply Z2Nat.inj_le; try lia.
      - apply Z2Nat.inj_le; try lia.
    }
    specialize (check_prime_aux_correct 196 197 (Z.to_nat n) Hrange Hcheck).
    intro Hgcd.
    rewrite <- (Z2Nat.id n) in Hgcd by lia.
    unfold rel_prime.
    rewrite Hgcd.
    apply Zgcd_is_gcd.
Qed.