Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.

Definition count_up_to_spec (n : nat) (ans : list nat) : Prop :=
  (forall x, In x ans -> 2 <= x < n /\ (forall d, 2 <= d < x -> x mod d <> 0)) /\
  (forall x, 2 <= x < n -> (forall d, 2 <= d < x -> x mod d <> 0) -> In x ans).

Example test_count_up_to_5: count_up_to_spec 5 [2; 3].
Proof.
  unfold count_up_to_spec.
  split.
  - (* Part 1: All elements in the list are primes < 5 *)
    intros x HIn.
    simpl in HIn.
    destruct HIn as [H2 | [H3 | HAbs]].
    + (* Case x = 2 *)
      subst x.
      split.
      * lia. (* 2 <= 2 < 5 *)
      * intros d Hd.
        lia. (* No d such that 2 <= d < 2 *)
    + (* Case x = 3 *)
      subst x.
      split.
      * lia. (* 2 <= 3 < 5 *)
      * intros d Hd.
        (* The only candidate for d is 2 *)
        assert (d = 2) by lia.
        subst d.
        simpl.
        discriminate. (* 3 mod 2 <> 0 *)
    + (* Case False (end of list) *)
      contradiction.
  
  - (* Part 2: All primes < 5 are in the list *)
    intros x HRange HPrime.
    (* The possible values for x are 2, 3, 4 *)
    assert (x = 2 \/ x = 3 \/ x = 4) as HCase by lia.
    destruct HCase as [H2 | [H3 | H4]].
    + (* Case x = 2 *)
      subst x.
      simpl. left. reflexivity.
    + (* Case x = 3 *)
      subst x.
      simpl. right. left. reflexivity.
    + (* Case x = 4 *)
      subst x.
      (* Prove that 4 is not prime to derive contradiction *)
      exfalso.
      specialize (HPrime 2).
      assert (2 <= 2 < 4) as HDiv by lia.
      apply HPrime in HDiv.
      simpl in HDiv.
      contradiction. (* 4 mod 2 = 0, so HDiv (which says <> 0) is false *)
Qed.