Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.

Definition count_up_to_spec (n : nat) (ans : list nat) : Prop :=
  (forall x, In x ans -> 2 <= x < n /\ (forall d, 2 <= d < x -> x mod d <> 0)) /\
  (forall x, 2 <= x < n -> (forall d, 2 <= d < x -> x mod d <> 0) -> In x ans).

Example test_case : count_up_to_spec 6 [2; 3; 5].
Proof.
  unfold count_up_to_spec.
  split.
  
  (* Part 1: Prove that all elements in [2; 3; 5] are primes < 6 *)
  - intros x H_in.
    simpl in H_in.
    destruct H_in as [H2 | [H3 | [H5 | H_absurd]]].
    
    (* Case x = 2 *)
    + subst x.
      split.
      * lia.
      * intros d H_range.
        lia.
        
    (* Case x = 3 *)
    + subst x.
      split.
      * lia.
      * intros d H_range.
        assert (d = 2) by lia.
        subst d.
        simpl.
        intro H_mod.
        discriminate.

    (* Case x = 5 *)
    + subst x.
      split.
      * lia.
      * intros d H_range.
        assert (d = 2 \/ d = 3 \/ d = 4) as H_d by lia.
        destruct H_d as [D2 | [D3 | D4]]; subst d; simpl; intro H_mod; discriminate.
        
    (* Case False (End of list) *)
    + contradiction.

  (* Part 2: Prove that all primes < 6 are in [2; 3; 5] *)
  - intros x H_bound H_prime.
    (* Since 2 <= x < 6, x must be 2, 3, 4, or 5 *)
    assert (x = 2 \/ x = 3 \/ x = 4 \/ x = 5) as H_cases by lia.
    destruct H_cases as [H2 | [H3 | [H4 | H5]]].
    
    (* Case x = 2 *)
    + subst x.
      simpl. left. reflexivity.
      
    (* Case x = 3 *)
    + subst x.
      simpl. right. left. reflexivity.
      
    (* Case x = 4 *)
    + subst x.
      (* 4 is not prime *)
      exfalso.
      specialize (H_prime 2).
      assert (H_div_range : 2 <= 2 < 4) by lia.
      apply H_prime in H_div_range.
      simpl in H_div_range.
      apply H_div_range.
      reflexivity.

    (* Case x = 5 *)
    + subst x.
      simpl. right. right. left. reflexivity.
Qed.