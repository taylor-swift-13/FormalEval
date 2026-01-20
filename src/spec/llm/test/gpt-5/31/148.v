Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition divides (d n : Z) : Prop :=
  exists k : Z, n = d * k.

Definition is_prime_pred (n : Z) : Prop :=
  2 <= n /\ forall i : Z, 2 <= i <= Z.sqrt n -> ~ divides i n.

Definition is_prime_spec (n : Z) (b : bool) : Prop :=
  (b = true <-> is_prime_pred n) /\ (b = false <-> ~ is_prime_pred n).

Lemma not_is_prime_neg76 : ~ is_prime_pred (-76%Z).
Proof.
  unfold is_prime_pred.
  intros [Hn _].
  lia.
Qed.

Example is_prime_spec_test_neg76 :
  is_prime_spec (-76%Z) false.
Proof.
  unfold is_prime_spec.
  split.
  - split; intro H.
    + exfalso. discriminate H.
    + exfalso. apply not_is_prime_neg76. assumption.
  - split; intro H.
    + apply not_is_prime_neg76.
    + reflexivity.
Qed.