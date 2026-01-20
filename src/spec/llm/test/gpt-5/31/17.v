Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition divides (d n : Z) : Prop :=
  exists k : Z, n = d * k.

Definition is_prime_pred (n : Z) : Prop :=
  2 <= n /\ forall i : Z, 2 <= i <= Z.sqrt n -> ~ divides i n.

Definition is_prime_spec (n : Z) (b : bool) : Prop :=
  (b = true <-> is_prime_pred n) /\ (b = false <-> ~ is_prime_pred n).

Lemma not_is_prime_40 : ~ is_prime_pred 40.
Proof.
  unfold is_prime_pred.
  intros [Hn Hforall].
  specialize (Hforall 2).
  assert (Hrange : 2 <= 2 <= Z.sqrt 40).
  { split; [lia|].
    assert (Hsqrt : Z.sqrt 40 = 6) by (vm_compute; reflexivity).
    rewrite Hsqrt. lia. }
  specialize (Hforall Hrange).
  apply Hforall.
  unfold divides.
  exists 20.
  simpl.
  reflexivity.
Qed.

Example is_prime_spec_test_40 :
  is_prime_spec 40 false.
Proof.
  unfold is_prime_spec.
  split.
  - split; intro H.
    + exfalso. discriminate H.
    + exfalso. apply not_is_prime_40. assumption.
  - split; intro H.
    + apply not_is_prime_40.
    + reflexivity.
Qed.