Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

(*
 * largest_prime_factor 函数的最终正确程序规约
 *)
(* Pre: n must be > 1 and not prime for this spec to be meaningful *)
Definition problem_59_pre (n : Z) : Prop := (Z.gt n 1 /\ ~ (prime n)).

Definition problem_59_spec (n p: Z) : Prop :=
  (* 后置条件: p 必须是 n 的最大素数因子 *)
  (
    (* 1. p 是 n 的一个素数因子 *)
    prime p /\ (p | n) /\

    (* 2. p 是最大的那一个 *)
    (* 对于任何其他的素数因子 q，q 都必须小于或等于 p *)
    (forall q: Z, (prime q /\ (q | n)) -> Z.le q p)
  ).

Example test_largest_prime_factor_15 : 
  problem_59_pre 15 -> problem_59_spec 15 5.
Proof.
  (* Unfold definitions *)
  unfold problem_59_pre, problem_59_spec.
  
  (* Prove the precondition: 15 > 1 and not prime *)
  intro H_pre.
  destruct H_pre as [H_gt H_not_prime].
  
  (* Prove the specification *)
  split; [|split].
  - (* Prove 5 is prime *)
    apply prime_intro.
    + (* 5 > 1 *) lia.
    + (* For all x dividing 5, x is a unit or 5/x is a unit *)
      intros x Hdiv.
      assert (x = 1 \/ x = -1 \/ x = 5 \/ x = -5) as Hcases.
      { 
        (* x must divide 5, so |x| ≤ 5 *)
        assert (Z.abs x ≤ 5) as Hbound.
        { apply Z.divide_bounds; try lia. exact Hdiv. }
        (* Check all possible divisors *)
        destruct (Z_lt_ge_dec 0 x) as [Hpos|Hneg].
        - (* x positive *)
          assert (1 ≤ x ≤ 5) by lia.
          destruct (Z.eq_dec x 1); [left; auto|].
          destruct (Z.eq_dec x 2); [contradict Hdiv; compute; lia|].
          destruct (Z.eq_dec x 3); [contradict Hdiv; compute; lia|].
          destruct (Z.eq_dec x 4); [contradict Hdiv; compute; lia|].
          destruct (Z.eq_dec x 5); [right; right; left; auto|].
          lia.
        - (* x non-positive *)
          assert (-5 ≤ x ≤ -1) by lia.
          destruct (Z.eq_dec x (-1)); [right; left; auto|].
          destruct (Z.eq_dec x (-2)); [contradict Hdiv; compute; lia|].
          destruct (Z.eq_dec x (-3)); [contradict Hdiv; compute; lia|].
          destruct (Z.eq_dec x (-4)); [contradict Hdiv; compute; lia|].
          destruct (Z.eq_dec x (-5)); [right; right; right; auto|].
          lia.
      }
      destruct Hcases as [H1|[[Hm1|[H5|Hm5]]]].
      * left. exists 1. lia.
      * left. exists (-1). lia.
      * right. exists 1. lia.
      * right. exists (-1). lia.
  - (* Prove 5 divides 15 *)
    exists 3. lia.
  - (* Prove 5 is the largest prime factor *)
    intros q (Hprime_q, Hdiv_q).
    (* Prime factors of 15: only 3 and 5 *)
    assert (q > 0) by (apply prime_ge_2; auto).
    assert (q ≤ 15) by (apply Z.divide_pos_le; lia).
    
    (* Enumerate possible prime divisors of 15 *)
    assert (q = 3 \/ q = 5) as Hcases.
    {
      (* Check which primes between 2 and 15 divide 15 *)
      destruct (Z.eq_dec q 2) as [H2|H2].
      { left. contradict Hdiv_q. compute. lia. }
      destruct (Z.eq_dec q 3) as [H3|H3].
      { left. auto. }
      destruct (Z.eq_dec q 5) as [H5|H5].
      { right. auto. }
      destruct (Z.eq_dec q 7) as [H7|H7].
      { contradict Hdiv_q. compute. lia. }
      destruct (Z.eq_dec q 11) as [H11|H11].
      { contradict Hdiv_q. compute. lia. }
      destruct (Z.eq_dec q 13) as [H13|H13].
      { contradict Hdiv_q. compute. lia. }
      
      (* If q is not one of these, it must be composite or out of range *)
      assert (2 ≤ q ≤ 15) by lia.
      (* Check if q is composite *)
      destruct (Z_lt_ge_dec q 2) as [Hlt|_]; try lia.
      destruct (Z_lt_ge_dec q 16) as [|Hgt]; try lia.
      exfalso.
      (* q must be composite since only primes 2,3,5,7,11,13 are in range *)
      assert (q = 4 \/ q = 6 \/ q = 8 \/ q = 9 \/ q = 10 \/ q = 12 \/ q = 14 \/ q = 15) as Hcomp.
      { lia. }
      destruct Hcomp as [H4|[H6|[H8|[H9|[H10|[H12|[H14|H15]]]]]]];
      subst q;
      try (apply not_prime_1; lia);
      try (apply not_prime_1; lia).
    }
    destruct Hcases; subst q; lia.
Qed.