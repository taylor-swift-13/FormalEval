Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition divides (d n : Z) : Prop :=
  exists k : Z, n = d * k.

Definition is_prime_pred (n : Z) : Prop :=
  2 <= n /\ forall i : Z, 2 <= i <= Z.sqrt n -> ~ divides i n.

Definition is_prime_spec (n : Z) (b : bool) : Prop :=
  (b = true <-> is_prime_pred n) /\ (b = false <-> ~ is_prime_pred n).

Lemma is_prime_101 : is_prime_pred 101.
Proof.
  unfold is_prime_pred.
  split.
  - lia.
  - intros i [Hi_low Hi_high] Hdiv.
    assert (Hsqrt : Z.sqrt 101 = 10) by (vm_compute; reflexivity).
    rewrite Hsqrt in Hi_high.
    destruct Hdiv as [k Heq].
    destruct (Z_le_gt_dec i 2) as [Hi_le2 | Hi_gt2].
    + assert (i = 2) by lia. subst i. lia.
    + destruct (Z_le_gt_dec i 3) as [Hi_le3 | Hi_gt3].
      * assert (i = 3) by lia. subst i. lia.
      * destruct (Z_le_gt_dec i 4) as [Hi_le4 | Hi_gt4].
        { assert (i = 4) by lia. subst i. lia. }
        { destruct (Z_le_gt_dec i 5) as [Hi_le5 | Hi_gt5].
          { assert (i = 5) by lia. subst i. lia. }
          { destruct (Z_le_gt_dec i 6) as [Hi_le6 | Hi_gt6].
            { assert (i = 6) by lia. subst i. lia. }
            { destruct (Z_le_gt_dec i 7) as [Hi_le7 | Hi_gt7].
              { assert (i = 7) by lia. subst i. lia. }
              { destruct (Z_le_gt_dec i 8) as [Hi_le8 | Hi_gt8].
                { assert (i = 8) by lia. subst i. lia. }
                { destruct (Z_le_gt_dec i 9) as [Hi_le9 | Hi_gt9].
                  { assert (i = 9) by lia. subst i. lia. }
                  { assert (i = 10) by lia. subst i. lia. }}}}}}
Qed.

Example is_prime_spec_test_101 :
  is_prime_spec 101 true.
Proof.
  unfold is_prime_spec.
  split.
  - split; intro H.
    + apply is_prime_101.
    + reflexivity.
  - split; intro H.
    + exfalso. discriminate H.
    + exfalso. apply H. apply is_prime_101.
Qed.