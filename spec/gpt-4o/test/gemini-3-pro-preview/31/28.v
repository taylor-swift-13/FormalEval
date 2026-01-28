Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import ListNotations.

(* Note: The specification provided in the description contained ambiguity 
   regarding the scope of quantifiers and implication. 
   Parentheses have been added to the hypotheses of the implications 
   to ensure the logical definition of primality is correct and provable. *)

Definition is_prime_spec (n : nat) (result : bool) : Prop :=
  (n <= 1 -> result = false) /\
  (n > 1 ->
   ((exists i, 2 <= i < n /\ n mod i = 0) -> result = false) /\
   ((forall i, 2 <= i < n -> n mod i <> 0) -> result = true)).

Example test_is_prime_1234566 : is_prime_spec 1234566 false.
Proof.
  unfold is_prime_spec.
  split.
  - intros. reflexivity.
  - intros _. split.
    + intros. reflexivity.
    + intros H_forall.
      (* We disprove the hypothesis that 1234566 is prime by showing 2 divides it *)
      assert (H_bounds : 2 <= 2 < 1234566).
      { 
        split.
        - apply le_n.
        - apply Nat.ltb_lt. vm_compute. reflexivity.
      }
      specialize (H_forall 2 H_bounds).
      assert (H_mod : 1234566 mod 2 = 0).
      { vm_compute. reflexivity. }
      rewrite H_mod in H_forall.
      contradiction.
Qed.