Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition divides (d n : Z) : Prop :=
  exists k : Z, n = d * k.

Definition is_prime_pred (n : Z) : Prop :=
  2 <= n /\ forall i : Z, 2 <= i <= Z.sqrt n -> ~ divides i n.

Definition is_prime_spec (n : Z) (b : bool) : Prop :=
  (b = true <-> is_prime_pred n) /\ (b = false <-> ~ is_prime_pred n).

Lemma not_is_prime_85 : ~ is_prime_pred 85.
Proof.
  unfold is_prime_pred.
  intros [Hn Hforall].
  specialize (Hforall 5).
  assert (Hrange : 2 <= 5 <= Z.sqrt 85).
  { split; [lia|].
    assert (Hsqrt : Z.sqrt 85 = 9) by (vm_compute; reflexivity).
    rewrite Hsqrt. lia. }
  specialize (Hforall Hrange).
  apply Hforall.
  unfold divides.
  exists 17.
  simpl.
  reflexivity.
Qed.

Example is_prime_spec_test_85 :
  is_prime_spec 85 false.
Proof.
  unfold is_prime_spec.
  split.
  - split; intro H.
    + exfalso. discriminate H.
    + exfalso. apply not_is_prime_85. assumption.
  - split; intro H.
    + apply not_is_prime_85.
    + reflexivity.
Qed.