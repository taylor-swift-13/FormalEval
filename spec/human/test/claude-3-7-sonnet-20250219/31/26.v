Require Import Arith.
Require Import Lia.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_is_prime_neg1 :
  problem_31_spec 0 false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  + (* -> direction: IsPrime 0 -> false = true (impossible) *)
    intros [Hgt _].
    lia.
  + (* <- direction: false = true -> IsPrime 0 (impossible) *)
    intros H.
    discriminate H.
Qed.