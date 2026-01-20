Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Lemma five_is_prime : is_prime 5.
Proof.
  unfold is_prime.
  split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2) as Hd by lia.
    subst d.
    compute. discriminate.
Qed.

Example test_x_or_y : x_or_y_spec 5 5 5 5.
Proof.
  unfold x_or_y_spec.
  split.
  - intros _. reflexivity.
  - intros _. reflexivity.
Qed.