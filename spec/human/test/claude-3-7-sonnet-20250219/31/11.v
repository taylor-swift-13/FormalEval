Require Import Arith.
Require Import Lia.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_is_prime_77 :
  problem_31_spec 77 false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  + (* -> direction: IsPrime 77 -> false = true (impossible) *)
    intros [Hgt Hdiv].
    assert (77 mod 7 = 0) by reflexivity.
    specialize (Hdiv 7 H).
    destruct Hdiv as [H7 | H7].
    - discriminate H7.
    - discriminate H7.
  + (* <- direction: false = true -> IsPrime 77 (impossible) *)
    intros H.
    discriminate H.
Qed.