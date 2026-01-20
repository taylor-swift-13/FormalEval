Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition divides (d n : Z) : Prop :=
  exists k : Z, n = d * k.

Definition is_prime_pred (n : Z) : Prop :=
  2 <= n /\ forall i : Z, 2 <= i <= Z.sqrt n -> ~ divides i n.

Definition is_prime_spec (n : Z) (b : bool) : Prop :=
  (b = true <-> is_prime_pred n) /\ (b = false <-> ~ is_prime_pred n).

Lemma not_is_prime_34983 : ~ is_prime_pred 34983.
Proof.
  unfold is_prime_pred.
  intros [Hn Hforall].
  specialize (Hforall 3).
  assert (Hrange : 2 <= 3 <= Z.sqrt 34983).
  { split; [lia|].
    assert (Hsqrt : Z.sqrt 34983 = 187) by (vm_compute; reflexivity).
    rewrite Hsqrt. lia. }
  specialize (Hforall Hrange).
  apply Hforall.
  unfold divides.
  exists 11661.
  vm_compute.
  reflexivity.
Qed.

Example is_prime_spec_test_34983 :
  is_prime_spec 34983 false.
Proof.
  unfold is_prime_spec.
  split.
  - split; intro H.
    + exfalso. discriminate H.
    + exfalso. apply not_is_prime_34983. assumption.
  - split; intro H.
    + apply not_is_prime_34983.
    + reflexivity.
Qed.