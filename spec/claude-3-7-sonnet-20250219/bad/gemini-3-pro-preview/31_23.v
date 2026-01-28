Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Definition divides (d n : nat) : Prop :=
  exists k, n = d * k.

Definition is_prime_spec (n : nat) (b : bool) : Prop :=
  b = true <-> 
    1 < n /\
    (forall d, 1 < d < n -> ~ divides d n).

Example test_is_prime_9000 : is_prime_spec 9000 false.
Proof.
  unfold is_prime_spec.
  split.
  - intro H. discriminate H.
  - intro H. destruct H as [H_gt_1 H_no_divisors].
    assert (H_div_2 : divides 2 9000).
    {
      unfold divides.
      exists 4500.
      lia.
    }
    assert (H_bounds : 1 < 2 < 9000).
    {
      lia.
    }
    specialize (H_no_divisors 2 H_bounds).
    contradiction.
Qed.