Require Import Arith.
Require Import Lia.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_is_prime_1008 :
  problem_31_spec 1008 false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  + (* -> direction: IsPrime 1008 -> false = true (impossible) *)
    intros [Hgt Hdiv].
    assert (1008 mod 2 = 0) by reflexivity.
    specialize (Hdiv 2 H).
    destruct Hdiv as [H2 | H2].
    - discriminate H2.
    - discriminate H2.
  + (* <- direction: false = true -> IsPrime 1008 (impossible) *)
    intros H.
    discriminate H.
Qed.