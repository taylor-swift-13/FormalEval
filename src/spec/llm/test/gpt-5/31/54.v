Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition divides (d n : Z) : Prop :=
  exists k : Z, n = d * k.

Definition is_prime_pred (n : Z) : Prop :=
  2 <= n /\ forall i : Z, 2 <= i <= Z.sqrt n -> ~ divides i n.

Definition is_prime_spec (n : Z) (b : bool) : Prop :=
  (b = true <-> is_prime_pred n) /\ (b = false <-> ~ is_prime_pred n).

Lemma is_prime_3 : is_prime_pred 3.
Proof.
  unfold is_prime_pred.
  split.
  - lia.
  - intros i Hrange.
    destruct Hrange as [Hi2 HiSqrt].
    assert (Hsqrt : Z.sqrt 3 = 1) by (vm_compute; reflexivity).
    rewrite Hsqrt in HiSqrt.
    unfold not.
    intros Hdiv.
    lia.
Qed.

Example is_prime_spec_test_3 :
  is_prime_spec 3 true.
Proof.
  unfold is_prime_spec.
  split.
  - split; intro H.
    + apply is_prime_3.
    + reflexivity.
  - split; intro H.
    + unfold not. intros HP. discriminate H.
    + exfalso. apply H. apply is_prime_3.
Qed.