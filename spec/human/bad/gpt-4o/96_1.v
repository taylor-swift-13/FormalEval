Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope nat_scope.
Open Scope Z_scope.

(* Function to check if a natural number is prime *)
Definition is_prime_nat (n : nat) : bool :=
  match n with
  | 0 | 1 => false
  | _ => Zis_prime (Z.of_nat n)
  end.

(* Convert the boolean result of is_prime_nat to a Prop *)
Lemma is_prime_nat_correct : forall n,
  is_prime_nat n = true <-> prime (Z.of_nat n).
Proof.
  intros n. unfold is_prime_nat.
  destruct n as [| [| n']]; simpl.
  - split; intros H; try discriminate; apply prime_2.
  - split; intros H; try discriminate; apply prime_2.
  - apply Zis_prime_spec.
Qed.

(* Function to count up to n primes less than n *)
Definition count_up_to (n : nat) : list nat :=
  filter is_prime_nat (seq 2 (n - 2)).

Lemma count_up_to_spec : forall n,
  problem_96_spec n (count_up_to n).
Proof.
  intros n.
  unfold problem_96_spec.
  split.
  - intros p H.
    unfold count_up_to in H.
    apply filter_In in H.
    destruct H as [_ Hprime].
    apply is_prime_nat_correct in Hprime.
    assumption.
  - split.
    + intros p H.
      unfold count_up_to in H.
      apply filter_In in H.
      destruct H as [H _].
      rewrite in_seq in H.
      lia.
    + split.
      * intros p Hprime Hp.
        unfold count_up_to.
        apply filter_In.
        rewrite in_seq.
        split.
        -- lia.
        -- apply is_prime_nat_correct.
           assumption.
      * split.
        -- unfold count_up_to.
           apply Sorted_StronglySorted.
           ++ intros x y Hxy.
              apply Nat.lt_strorder.
           ++ apply filter_sorted.
              apply seq_sorted.
        -- unfold count_up_to.
           apply NoDup_filter.
           apply seq_NoDup.
Qed.

Example test_count_up_to_5 : count_up_to 5 = [2; 3].
Proof.
  unfold count_up_to.
  simpl.
  reflexivity.
Qed.

Qed.