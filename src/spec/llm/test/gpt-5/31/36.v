Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition divides (d n : Z) : Prop :=
  exists k : Z, n = d * k.

Definition is_prime_pred (n : Z) : Prop :=
  2 <= n /\ forall i : Z, 2 <= i <= Z.sqrt n -> ~ divides i n.

Definition is_prime_spec (n : Z) (b : bool) : Prop :=
  (b = true <-> is_prime_pred n) /\ (b = false <-> ~ is_prime_pred n).

Lemma is_prime_37 : is_prime_pred 37.
Proof.
  unfold is_prime_pred.
  split; [lia|].
  intros i [Hi_lo Hi_hi].
  assert (Hsqrt : Z.sqrt 37 = 6) by (vm_compute; reflexivity).
  rewrite Hsqrt in Hi_hi.
  unfold not.
  intros [k Hk].
  destruct (Z.eq_dec i 2) as [Hi2|Hneq2].
  - subst i. lia.
  - assert (3 <= i) by lia.
    destruct (Z.eq_dec i 3) as [Hi3|Hneq3].
    + subst i. lia.
    + assert (4 <= i) by lia.
      destruct (Z.eq_dec i 4) as [Hi4|Hneq4].
      * subst i. lia.
      * assert (5 <= i) by lia.
        destruct (Z.eq_dec i 5) as [Hi5|Hneq5].
        { subst i. lia. }
        assert (6 <= i) by lia.
        destruct (Z.eq_dec i 6) as [Hi6|Hneq6].
        { subst i. lia. }
        assert (7 <= i) by lia.
        lia.
Qed.

Example is_prime_spec_test_37 :
  is_prime_spec 37 true.
Proof.
  unfold is_prime_spec.
  split.
  - split; intro H.
    + exact is_prime_37.
    + reflexivity.
  - split; intro H.
    + exfalso. discriminate H.
    + exfalso. apply H. exact is_prime_37.
Qed.