Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.

Definition count_up_to_spec (n : nat) (ans : list nat) : Prop :=
  (forall x, In x ans -> 2 <= x < n /\ (forall d, 2 <= d < x -> x mod d <> 0)) /\
  (forall x, 2 <= x < n -> (forall d, 2 <= d < x -> x mod d <> 0) -> In x ans).

Example test_case : count_up_to_spec 5 [2; 3].
Proof.
  unfold count_up_to_spec.
  split.
  
  (* Part 1: Prove that all elements in [2; 3] are primes < 5 *)
  - intros x H_in.
    simpl in H_in.
    destruct H_in as [H2 | [H3 | H_absurd]].
    
    (* Case x = 2 *)
    + subst x.
      split.
      * lia. (* 2 <= 2 < 5 *)
      * intros d H_range.
        (* Range 2 <= d < 2 is empty *)
        lia.
        
    (* Case x = 3 *)
    + subst x.
      split.
      * lia. (* 2 <= 3 < 5 *)
      * intros d H_range.
        (* Range 2 <= d < 3 implies d = 2 *)
        assert (d = 2) by lia.
        subst d.
        (* Check 3 mod 2 <> 0 *)
        simpl.
        intro H_mod.
        discriminate.
        
    (* Case False (End of list) *)
    + contradiction.

  (* Part 2: Prove that all primes < 5 are in [2; 3] *)
  - intros x H_bound H_prime.
    (* Since 2 <= x < 5, x must be 2, 3, or 4 *)
    assert (x = 2 \/ x = 3 \/ x = 4) as H_cases by lia.
    destruct H_cases as [H2 | [H3 | H4]].
    
    (* Case x = 2 *)
    + subst x.
      simpl. left. reflexivity.
      
    (* Case x = 3 *)
    + subst x.
      simpl. right. left. reflexivity.
      
    (* Case x = 4 *)
    + subst x.
      (* 4 is not prime, so this case implies a contradiction with H_prime *)
      exfalso.
      (* We show that 2 divides 4, violating the primality condition *)
      specialize (H_prime 2).
      assert (H_div_range : 2 <= 2 < 4) by lia.
      apply H_prime in H_div_range.
      simpl in H_div_range.
      (* 4 mod 2 = 0, but hypothesis says <> 0 *)
      apply H_div_range.
      reflexivity.
Qed.