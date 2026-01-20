Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition divides (d n : Z) : Prop :=
  exists k : Z, n = d * k.

Definition is_prime_pred (n : Z) : Prop :=
  2 <= n /\ forall i : Z, 2 <= i <= Z.sqrt n -> ~ divides i n.

Definition is_prime_spec (n : Z) (b : bool) : Prop :=
  (b = true <-> is_prime_pred n) /\ (b = false <-> ~ is_prime_pred n).

Lemma is_prime_11 : is_prime_pred 11.
Proof.
  unfold is_prime_pred.
  split.
  - lia.
  - intros i Hi Hdiv.
    destruct Hi as [Hi_low Hi_high].
    assert (Hsqrt : Z.sqrt 11 = 3) by (vm_compute; reflexivity).
    rewrite Hsqrt in Hi_high.
    destruct Hdiv as [k Hk].
    destruct (Z.eq_dec i 2) as [Heq | Hneq].
    + subst i. lia.
    + assert (2 < i) by lia.
      assert (i = 3) by lia.
      subst i. lia.
Qed.

Example is_prime_spec_test_11 :
  is_prime_spec 11 true.
Proof.
  unfold is_prime_spec.
  split.
  - split; intro H.
    + apply is_prime_11.
    + reflexivity.
  - split; intro H.
    + exfalso. discriminate H.
    + exfalso. apply H. apply is_prime_11.
Qed.