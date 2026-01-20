Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition divides (d n : Z) : Prop :=
  exists k : Z, n = d * k.

Definition is_prime_pred (n : Z) : Prop :=
  2 <= n /\ forall i : Z, 2 <= i <= Z.sqrt n -> ~ divides i n.

Definition is_prime_spec (n : Z) (b : bool) : Prop :=
  (b = true <-> is_prime_pred n) /\ (b = false <-> ~ is_prime_pred n).

Lemma not_is_prime_minus_91 : ~ is_prime_pred (-91).
Proof.
  unfold is_prime_pred.
  intros [Hn Hforall].
  lia.
Qed.

Example is_prime_spec_test_minus_91 :
  is_prime_spec (-91) false.
Proof.
  unfold is_prime_spec.
  split.
  - split; intro H.
    + exfalso. discriminate H.
    + exfalso. apply not_is_prime_minus_91. assumption.
  - split; intro H.
    + apply not_is_prime_minus_91.
    + reflexivity.
Qed.