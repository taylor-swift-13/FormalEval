Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.

Definition count_up_to_spec (n : nat) (ans : list nat) : Prop :=
  (forall x, In x ans -> 2 <= x < n /\ (forall d, 2 <= d < x -> x mod d <> 0)) /\
  (forall x, 2 <= x < n -> (forall d, 2 <= d < x -> x mod d <> 0) -> In x ans).

Example test_case : count_up_to_spec 3 [2].
Proof.
  unfold count_up_to_spec.
  split.
  
  - intros x H_in.
    simpl in H_in.
    destruct H_in as [H2 | H_absurd].
    
    + subst x.
      split.
      * lia.
      * intros d H_range.
        lia.
        
    + contradiction.

  - intros x H_bound H_prime.
    assert (x = 2) as H_eq by lia.
    subst x.
    simpl. left. reflexivity.
Qed.