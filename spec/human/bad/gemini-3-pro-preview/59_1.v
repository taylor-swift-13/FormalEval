Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

(* Definition of the precondition *)
Definition problem_59_pre (n : Z) : Prop := (Z.gt n 1 /\ ~ (prime n)).

(* Definition of the specification *)
Definition problem_59_spec (n p: Z) : Prop :=
  (* p is a prime factor of n *)
  (prime p /\ (p | n) /\
  (* p is the largest prime factor *)
  (forall q: Z, (prime q /\ (q | n)) -> Z.le q p)).

(* Example test case verification *)
Example test_problem_59_15 : problem_59_spec 15 5.
Proof.
  (* Unfold the specification *)
  unfold problem_59_spec.
  split.
  
  - (* Part 1: Prove 5 is a prime factor of 15 *)
    split.
    + (* Prove 5 is prime *)
      apply prime_intro.
      * (* 1 < 5 *)
        lia.
      * (* gcd(n, 5) = 1 for 1 <= n < 5 *)
        intros n Hn.
        (* Convert relative primality to GCD = 1 condition *)
        apply Zgcd_1_rel_prime.
        (* Enumerate possible values for n *)
        assert (H_cases: n = 1 \/ n = 2 \/ n = 3 \/ n = 4) by lia.
        destruct H_cases as [-> | [-> | [-> | ->]]];
        (* Prove GCD is 1 by computation *)
        compute; reflexivity.
    + (* Prove 5 divides 15 *)
      exists 3. reflexivity.

  - (* Part 2: Prove 5 is the largest prime factor *)
    intros q [H_prime_q H_div_q].
    
    (* Decompose 15 into 3 * 5 *)
    replace 15 with (3 * 5) in H_div_q by reflexivity.
    
    (* Since q is prime and divides 3 * 5, q must divide 3 or 5 *)
    apply prime_mult in H_div_q; [| exact H_prime_q].
    
    destruct H_div_q as [H_div_3 | H_div_5].
    + (* Case: q divides 3 *)
      (* Since 3 > 0, a divisor q must be <= 3 *)
      apply Z.divide_pos_le in H_div_3; [| lia].
      lia. (* q <= 3 <= 5 *)
    + (* Case: q divides 5 *)
      (* Since 5 > 0, a divisor q must be <= 5 *)
      apply Z.divide_pos_le in H_div_5; [| lia].
      lia. (* q <= 5 *)
Qed.