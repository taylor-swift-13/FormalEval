Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope nat_scope.

(* n is a natural number (non-negative) *)
Definition problem_96_pre (n : nat) : Prop := True.

Definition problem_96_spec (n : nat) (result : list nat) : Prop :=
  (* Property 1: All elements in the result list are prime *)
  (forall p, In p result -> prime (Z.of_nat p)) /\

  (* Property 2: All elements in the result list are strictly less than n *)
  (forall p, In p result -> p < n) /\

  (* Property 3: All primes strictly less than n are in the result list (Completeness) *)
  (forall p, prime (Z.of_nat p) -> p < n -> In p result) /\

  (* Property 4: The list is strictly sorted (ascending) *)
  Sorted lt result /\

  (* Property 5: No duplicate elements in the list *)
  NoDup result.

(* Test case: input = 5, output = [2; 3] *)
Example test_case : problem_96_spec 5 [2; 3].
Proof.
  unfold problem_96_spec.
  split.
  (* 1. All elements are prime *)
  - intros p H_in.
    simpl in H_in.
    destruct H_in as [H_eq | [H_eq | H_false]].
    + subst p. apply prime_2.
    + subst p. apply prime_3.
    + contradiction.

  - split.
  (* 2. All elements < 5 *)
    + intros p H_in.
      simpl in H_in.
      destruct H_in as [H_eq | [H_eq | H_false]]; subst; lia.

    + split.
  (* 3. All primes < 5 are in the list *)
      * intros p H_prime H_lt.
        (* Analyze p based on p < 5 *)
        assert (H_cases: p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4) by lia.
        destruct H_cases as [ | [ | [ | [ | ]]]]; subst p.
        -- (* p = 0 *)
           apply prime_ge_2 in H_prime. simpl in H_prime. lia.
        -- (* p = 1 *)
           apply prime_ge_2 in H_prime. simpl in H_prime. lia.
        -- (* p = 2 *)
           simpl. left. reflexivity.
        -- (* p = 3 *)
           simpl. right. left. reflexivity.
        -- (* p = 4 *)
           exfalso.
           (* 4 is not prime *)
           inversion H_prime as [_ H_rel].
           specialize (H_rel 2%Z).
           assert (H_range: (1 <= 2 < 4)%Z) by lia.
           specialize (H_rel H_range).
           unfold rel_prime in H_rel.
           simpl in H_rel.
           discriminate.

      * split.
  (* 4. Sorted lt *)
        -- apply Sorted_cons.
           ++ apply Sorted_cons.
              ** apply Sorted_nil.
              ** apply HdRel_nil.
           ++ apply HdRel_cons. lia.

  (* 5. NoDup *)
        -- apply NoDup_cons.
           ++ simpl. intuition.
           ++ apply NoDup_cons.
              ** simpl. intuition.
              ** apply NoDup_nil.
Qed.