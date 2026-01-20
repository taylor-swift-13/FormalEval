Require Import List.
Require Import Arith.
Require Import Lia.
Require Import PeanoNat.

Import ListNotations.

Definition count_up_to_spec (n : nat) (ans : list nat) : Prop :=
  (forall x, In x ans -> 2 <= x < n /\ (forall d, 2 <= d < x -> x mod d <> 0)) /\
  (forall x, 2 <= x < n -> (forall d, 2 <= d < x -> x mod d <> 0) -> In x ans).

Example count_up_to_5 : count_up_to_spec 5 [2; 3].
Proof.
  unfold count_up_to_spec.
  split.
  - (* First part: all elements in the list are primes < n *)
    intros x Hin.
    simpl in Hin.
    destruct Hin as [H | [H | H]].
    + (* x = 2 *)
      subst x.
      split.
      * lia.
      * intros d Hd. lia.
    + (* x = 3 *)
      subst x.
      split.
      * lia.
      * intros d Hd.
        assert (d = 2) by lia.
        subst d. simpl. lia.
    + (* contradiction *)
      contradiction.
  - (* Second part: all primes < n are in the list *)
    intros x Hbound Hprime.
    simpl.
    assert (x = 2 \/ x = 3 \/ x = 4) as Hcases by lia.
    destruct Hcases as [H2 | [H3 | H4]].
    + (* x = 2 *)
      left. symmetry. exact H2.
    + (* x = 3 *)
      right. left. symmetry. exact H3.
    + (* x = 4: contradiction, 4 is not prime *)
      subst x.
      exfalso.
      specialize (Hprime 2).
      assert (2 <= 2 < 4) by lia.
      specialize (Hprime H).
      simpl in Hprime. lia.
Qed.