Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition problem_40_pre (input : list Z) : Prop := True.

Definition problem_40_spec (input : list Z) (output : bool) : Prop :=
  (exists i j k : nat,
    i <> j /\ i <> k /\ j <> k /\
    i < length input /\ j < length input /\ k < length input /\
    nth i input 0 + nth j input 0 + nth k input 0 = 0)
  <-> (output = true).

Example problem_40_test_1 :
  problem_40_spec [1%Z; 3%Z; 5%Z; 0%Z] false.
Proof.
  unfold problem_40_spec.
  split.
  - intros [i [j [k [Hij [Hik [Hjk [Hi_len [Hj_len [Hk_len Hsum]]]]]]]]].
    (* We want to show this leads to contradiction since no such triple sums to zero *)
    (* Length of input is 4, elements are [1;3;5;0] *)
    assert (Hi_lt4 : (i < 4)%nat) by assumption.
    assert (Hj_lt4 : (j < 4)%nat) by assumption.
    assert (Hk_lt4 : (k < 4)%nat) by assumption.
    (* We do case analysis on indices *)
    (* Since list is small, enumerate all possibilities *)

    (* Extract elements at positions i,j,k *)
    remember (nth i [1; 3; 5; 0] 0) as xi.
    remember (nth j [1; 3; 5; 0] 0) as xj.
    remember (nth k [1; 3; 5; 0] 0) as xk.

    (* Because i,j,k distinct and < 4, xi,xj,xk ∈ {1,3,5,0} with distinct indices *)
    (* We prove no sum xi + xj + xk = 0 holds for distinct i,j,k in [0..3] *)

    (* We enumerate all possible distinct triples *)

    (* Construct a lemma here to avoid repetition *)
    assert (Hno_zero_sum:
      forall i j k,
      i <> j -> j <> k -> i <> k ->
      (i < 4)%nat -> (j < 4)%nat -> (k < 4)%nat ->
      nth i [1;3;5;0] 0 + nth j [1;3;5;0] 0 + nth k [1;3;5;0] 0 <> 0).
    {
      intros ii jj kk Hneq1 Hneq2 Hneq3 Hii Hjj Hkk.
      (* By case analysis *)
      destruct ii; destruct jj; destruct kk; simpl; try lia;
      try contradict Hneq1; try contradict Hneq2; try contradict Hneq3;
      (* distinctness ensured by contradiction elimination above *)
      try lia.
      all: (* now enumerate sum *)
      (* The sums below cannot be zero *)
      (* 1+3+5=9 *)
      try (lia).
      (* 1+3+0=4 *)
      try (lia).
      (* 1+5+0=6 *)
      try (lia).
      (* 3+5+0=8 *)
      try (lia).
    }
    specialize (Hno_zero_sum i j k Hij Hjk Hik Hi_lt4 Hj_lt4 Hk_lt4).
    rewrite Heqxi in Hno_zero_sum.
    rewrite Heqxj in Hno_zero_sum.
    rewrite Heqxk in Hno_zero_sum.
    contradiction.
  - intros Hout.
    discriminate.
Qed.