Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
Import ListNotations.
Open Scope nat_scope.

Definition problem_96_pre (n : nat) : Prop := True.

Definition problem_96_spec (n : nat) (result : list nat) : Prop :=
  (forall p, In p result -> prime (Z.of_nat p)) /\
  (forall p, In p result -> p < n) /\
  (forall p, prime (Z.of_nat p) -> p < n -> In p result) /\
  Sorted lt result /\
  NoDup result.

(* Helper lemma: 2 is prime *)
Lemma prime_2 : prime 2%Z.
Proof.
  constructor.
  - lia.
  - intros n Hn Hdiv.
    assert (0 < n)%Z as Hpos by lia.
    apply Z.divide_pos_le in Hdiv; try lia.
    assert (n = 1 \/ n = 2)%Z as Hcases by lia.
    destruct Hcases; [left | right]; auto.
Qed.

(* Helper lemma: 3 is prime *)
Lemma prime_3 : prime 3%Z.
Proof.
  constructor.
  - lia.
  - intros n Hn Hdiv.
    assert (0 < n)%Z as Hpos by lia.
    apply Z.divide_pos_le in Hdiv; try lia.
    assert (n = 1 \/ n = 2 \/ n = 3)%Z as Hcases by lia.
    destruct Hcases as [H1 | [H2 | H3]].
    + left; auto.
    + exfalso. subst n. destruct Hdiv as [k Hk]. lia.
    + right; auto.
Qed.

(* 0 is not prime *)
Lemma not_prime_0 : ~prime 0%Z.
Proof.
  intro H. inversion H. lia.
Qed.

(* 1 is not prime *)
Lemma not_prime_1 : ~prime 1%Z.
Proof.
  intro H. inversion H. lia.
Qed.

(* 4 is not prime *)
Lemma not_prime_4 : ~prime 4%Z.
Proof.
  intro H.
  inversion H as [Hge Hrel].
  assert (H2: (2 | 4)%Z) by (exists 2%Z; lia).
  specialize (Hrel 2%Z ltac:(lia) H2).
  lia.
Qed.

Example test_count_up_to_5 : problem_96_spec 5 [2; 3].
Proof.
  unfold problem_96_spec.
  repeat split.
  - (* All elements are prime *)
    intros p Hp.
    simpl in Hp.
    destruct Hp as [Hp | [Hp | Hp]]; try contradiction.
    + subst p. exact prime_2.
    + subst p. exact prime_3.
  - (* All elements < 5 *)
    intros p Hp.
    simpl in Hp.
    destruct Hp as [Hp | [Hp | Hp]]; try contradiction; subst p; lia.
  - (* Completeness: all primes < 5 are in the list *)
    intros p Hprime Hlt.
    simpl.
    destruct p as [|[|[|[|[|p']]]]].
    + (* p = 0 *) exfalso. apply not_prime_0. exact Hprime.
    + (* p = 1 *) exfalso. apply not_prime_1. exact Hprime.
    + (* p = 2 *) left. reflexivity.
    + (* p = 3 *) right. left. reflexivity.
    + (* p = 4 *) exfalso. apply not_prime_4. exact Hprime.
    + (* p >= 5 *) lia.
  - (* Sorted *)
    apply Sorted_cons.
    + apply Sorted_cons.
      * apply Sorted_nil.
      * apply HdRel_nil.
    + apply HdRel_cons. lia.
  - (* NoDup *)
    apply NoDup_cons.
    + simpl. intros [H | [H | H]]; try discriminate; try contradiction.
    + apply NoDup_cons.
      * simpl. intros [H | H]; try discriminate; try contradiction.
      * apply NoDup_nil.
Qed.