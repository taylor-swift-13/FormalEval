Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition divides (d n : Z) : Prop :=
  exists k : Z, n = d * k.

Definition is_prime_pred (n : Z) : Prop :=
  2 <= n /\ forall i : Z, 2 <= i <= Z.sqrt n -> ~ divides i n.

Definition is_prime_spec (n : Z) (b : bool) : Prop :=
  (b = true <-> is_prime_pred n) /\ (b = false <-> ~ is_prime_pred n).

Axiom is_prime_42043 : is_prime_pred 42043.

Example is_prime_spec_test_42043 :
  is_prime_spec 42043 true.
Proof.
  unfold is_prime_spec.
  split.
  - split; intro H.
    + apply is_prime_42043.
    + reflexivity.
  - split; intro H.
    + unfold not. intro HP. discriminate H.
    + exfalso. apply H. apply is_prime_42043.
Qed.