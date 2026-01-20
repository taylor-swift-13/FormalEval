Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Lemma prime_113 : is_prime 113.
Proof.
  unfold is_prime.
  split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10) as Hd by lia.
    destruct Hd as [Hd | [Hd | [Hd | [Hd | [Hd | [Hd | [Hd | [Hd | Hd]]]]]]]];
    subst d; compute; discriminate.
Qed.

Example test_x_or_y : x_or_y_spec 113 200 200 200.
Proof.
  unfold x_or_y_spec.
  split.
  - intros _. reflexivity.
  - intros _. reflexivity.
Qed.