Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Lemma fortyone_is_prime : is_prime 41.
Proof.
  unfold is_prime.
  split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) as Hd by lia.
    destruct Hd as [Hd | [Hd | [Hd | [Hd | Hd]]]]; subst d; compute; discriminate.
Qed.

Example test_x_or_y : x_or_y_spec 41 199 24 199.
Proof.
  unfold x_or_y_spec.
  split.
  - intros _. reflexivity.
  - intros Hnot_prime.
    exfalso.
    apply Hnot_prime.
    exact fortyone_is_prime.
Qed.