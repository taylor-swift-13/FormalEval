Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope nat_scope.
Open Scope Z_scope.

Definition problem_96_spec (n : nat) (result : list nat) : Prop :=
  (* 1: all elements are prime *)
  (forall p, In p result -> prime (Z.of_nat p)) /\
  (* 2: all elements < n *)
  (forall p, In p result -> p < n) /\
  (* 3: completeness: all primes < n in result *)
  (forall z : Z, prime z -> 0 <= z < Z.of_nat n -> In (Z.to_nat z) result) /\
  (* 4: strictly ascending *)
  Sorted lt result /\
  (* 5: No duplicates *)
  NoDup result.

Example problem_96_test_5 :
  problem_96_spec 5 [2;3].
Proof.
  unfold problem_96_spec.
  repeat split.
  - (* all elements prime *)
    intros p Hp.
    simpl in Hp.
    destruct Hp as [Hp | [Hp | Hp]]; try contradiction.
    + apply prime_2.
    + (* prove prime 3 *)
      unfold prime.
      simpl.
      compute.
      reflexivity.
  - (* all elements < 5 *)
    intros p Hp.
    simpl in Hp.
    destruct Hp as [Hp | [Hp | Hp]]; try contradiction; lia.
  - (* completeness: all primes z with 0 <= z < 5 appear *)
    intros z Hz Hzrange.
    (* Since primes < 5 are 2 and 3 *)
    assert (z = 2 \/ z = 3).
    {
      assert (z >= 2) by (apply prime_ge_2; lia).
      destruct (Z.eq_dec z 2) as [Heq2|Hneq2]; [left; assumption |].
      destruct (Z.eq_dec z 3) as [Heq3|Hneq3]; [right; assumption|].
      (* Otherwise no other primes < 5 *)
      exfalso.
      assert (z <= 4) by lia.
      (* Check if prime 4 *)
      (* 4 is not prime *)
      assert (~ prime 4).
      {
        unfold not; intro Hpr.
        pose proof prime_divisors_unique 4 2 2 Hpr.
        lia.
      }
      apply H0; auto.
    }
    destruct H as [H2 | H3].
    + subst. simpl. left; reflexivity.
    + subst. simpl. right; left; reflexivity.
  - (* Sorted lt [2;3] *)
    simpl. constructor. constructor.
  - (* NoDup [2;3] *)
    simpl. constructor. constructor.
Qed.