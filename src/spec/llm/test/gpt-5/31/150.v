Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition divides (d n : Z) : Prop :=
  exists k : Z, n = d * k.

Definition is_prime_pred (n : Z) : Prop :=
  2 <= n /\ forall i : Z, 2 <= i <= Z.sqrt n -> ~ divides i n.

Definition is_prime_spec (n : Z) (b : bool) : Prop :=
  (b = true <-> is_prime_pred n) /\ (b = false <-> ~ is_prime_pred n).

Lemma not_is_prime_10000000032 : ~ is_prime_pred 10000000032.
Proof.
  unfold is_prime_pred.
  intros [Hn Hforall].
  specialize (Hforall 2).
  assert (Hrange : 2 <= 2 <= Z.sqrt 10000000032).
  { split; [lia|].
    assert (Hsqrt : Z.sqrt 10000000032 = 100000) by (vm_compute; reflexivity).
    rewrite Hsqrt. lia. }
  specialize (Hforall Hrange).
  apply Hforall.
  unfold divides.
  exists 5000000016.
  vm_compute.
  reflexivity.
Qed.

Example is_prime_spec_test_10000000032 :
  is_prime_spec 10000000032 false.
Proof.
  unfold is_prime_spec.
  split.
  - split; intro H.
    + exfalso. discriminate H.
    + exfalso. apply not_is_prime_10000000032. assumption.
  - split; intro H.
    + apply not_is_prime_10000000032.
    + reflexivity.
Qed.