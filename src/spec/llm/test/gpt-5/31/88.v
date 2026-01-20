Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition divides (d n : Z) : Prop :=
  exists k : Z, n = d * k.

Definition is_prime_pred (n : Z) : Prop :=
  2 <= n /\ forall i : Z, 2 <= i <= Z.sqrt n -> ~ divides i n.

Definition is_prime_spec (n : Z) (b : bool) : Prop :=
  (b = true <-> is_prime_pred n) /\ (b = false <-> ~ is_prime_pred n).

Lemma is_prime_23 : is_prime_pred 23.
Proof.
  unfold is_prime_pred.
  split.
  - lia.
  - intros i Hi Hdiv.
    destruct Hi as [Hi_low Hi_high].
    assert (Hsqrt : Z.sqrt 23 = 4) by (vm_compute; reflexivity).
    rewrite Hsqrt in Hi_high.
    destruct Hdiv as [k Hk].
    destruct (Z_le_gt_dec i 3) as [Hi_le3 | Hi_gt3].
    + destruct (Z_le_gt_dec i 2) as [Hi_le2 | Hi_gt2].
      * assert (i = 2) by lia. subst. lia.
      * assert (i = 3) by lia. subst. lia.
    + assert (i = 4) by lia. subst. lia.
Qed.

Example is_prime_spec_test_23 :
  is_prime_spec 23 true.
Proof.
  unfold is_prime_spec.
  split.
  - split; intro H.
    + apply is_prime_23.
    + reflexivity.
  - split; intro H.
    + exfalso. discriminate H.
    + exfalso. apply H. apply is_prime_23.
Qed.