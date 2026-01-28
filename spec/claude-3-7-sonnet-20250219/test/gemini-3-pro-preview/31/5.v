Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Definition divides (d n : nat) : Prop :=
  exists k, n = d * k.

Definition is_prime_spec (n : nat) (b : bool) : Prop :=
  b = true <-> 
    1 < n /\
    (forall d, 1 < d < n -> ~ divides d n).

Example test_is_prime_61 : is_prime_spec 61 true.
Proof.
  unfold is_prime_spec.
  split.
  - intro. split.
    + lia.
    + intros d Hbounds [k Hk].
      do 61 (destruct d; [ lia | ]).
      lia.
  - intro. reflexivity.
Qed.