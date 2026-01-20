Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition divides (d n : Z) : Prop :=
  exists k : Z, n = d * k.

Definition is_prime_pred (n : Z) : Prop :=
  2 <= n /\ forall i : Z, 2 <= i <= Z.sqrt n -> ~ divides i n.

Definition is_prime_spec (n : Z) (b : bool) : Prop :=
  (b = true <-> is_prime_pred n) /\ (b = false <-> ~ is_prime_pred n).

Lemma is_prime_5 : is_prime_pred 5.
Proof.
  unfold is_prime_pred.
  split.
  - lia.
  - intros i Hi.
    destruct Hi as [HiL HiU].
    assert (Hsqrt : Z.sqrt 5 = 2) by (vm_compute; reflexivity).
    rewrite Hsqrt in HiU.
    assert (Hi_eq : i = 2) by lia.
    subst i.
    unfold divides.
    intros [k Hk].
    destruct (Z_le_gt_dec k 2) as [Hle|Hgt].
    + assert (2 * k <= 4) by lia.
      rewrite <- Hk in H.
      lia.
    + assert (6 <= 2 * k) by lia.
      rewrite <- Hk in H.
      lia.
Qed.

Example is_prime_spec_test_5 :
  is_prime_spec 5 true.
Proof.
  unfold is_prime_spec.
  split.
  - split; intro H.
    + apply is_prime_5.
    + reflexivity.
  - split; intro H.
    + exfalso. discriminate H.
    + exfalso. apply H. apply is_prime_5.
Qed.