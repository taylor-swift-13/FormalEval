Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Definition divides (d n : nat) : Prop :=
  exists k, n = d * k.

Definition is_prime_spec (n : nat) (b : bool) : Prop :=
  b = true <-> 
    1 < n /\
    (forall d, 1 < d < n -> ~ divides d n).

Example test_is_prime_6 : is_prime_spec 6 false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    discriminate H.
  - (* Right to Left: ... -> false = true *)
    intros [H_gt1 H_no_divisors].
    (* We prove a contradiction by showing 2 divides 6 *)
    assert (H_div2: divides 2 6).
    {
      unfold divides.
      exists 3.
      reflexivity. 
    }
    assert (H_bounds: 1 < 2 < 6).
    {
      lia.
    }
    (* Apply the hypothesis H_no_divisors to 2 *)
    specialize (H_no_divisors 2 H_bounds).
    contradiction.
Qed.