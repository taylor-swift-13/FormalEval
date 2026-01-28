Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Definition divides (d n : nat) : Prop :=
  exists k, n = d * k.

Definition is_prime_spec (n : nat) (b : bool) : Prop :=
  b = true <-> 
    1 < n /\
    (forall d, 1 < d < n -> ~ divides d n).

Example test_is_prime_33 : is_prime_spec 33 false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: false = true -> ... *)
    intro H.
    discriminate H.
  - (* Case: ... -> false = true *)
    intro H.
    destruct H as [H_gt_1 H_no_divisors].
    (* We prove 33 is not prime by finding a divisor (3) *)
    assert (H_div_3 : divides 3 33).
    {
      unfold divides.
      exists 11.
      simpl.
      reflexivity.
    }
    assert (H_bounds : 1 < 3 < 33).
    {
      lia.
    }
    (* The specification claims no such divisor exists *)
    specialize (H_no_divisors 3 H_bounds).
    contradiction.
Qed.