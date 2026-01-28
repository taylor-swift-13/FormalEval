Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope nat_scope.
Open Scope Z_scope.

Definition problem_96_pre (n : nat) : Prop := True.

Definition problem_96_spec (n : nat) (result : list nat) : Prop :=
  (forall p, In p result -> prime (Z.of_nat p)) /\
  (forall p, In p result -> p < n) /\
  (forall p, prime (Z.of_nat p) -> p < n -> In p result) /\
  Sorted lt result /\
  NoDup result.

Lemma not_prime_0 : ~ prime 0%Z.
Proof.
  intros H.
  destruct H as [Hge2 _].
  lia.
Qed.

Lemma not_prime_1 : ~ prime 1%Z.
Proof.
  intros H.
  destruct H as [Hge2 _].
  lia.
Qed.

Lemma not_prime_4 : ~ prime 4%Z.
Proof.
  intros H.
  destruct H as [Hge2 Hfac].
  specialize (Hfac 2%Z 2%Z).
  assert (4%Z = 2%Z * 2%Z) by lia.
  specialize (Hfac H).
  destruct Hfac as [H1 | [H2 | [H3 | H4]]]; lia.
Qed.

Example problem_96_test_5 :
  problem_96_spec 5 [2; 3].
Proof.
  unfold problem_96_spec.
  repeat split.
  - intros p Hin.
    simpl in Hin.
    destruct Hin as [H2 | [H3 | []]]; subst; simpl.
    + apply prime_2.
    + apply prime_3.
  - intros p Hin.
    simpl in Hin.
    destruct Hin as [H2 | [H3 | []]]; subst; lia.
  - intros p Hp Hlt.
    destruct p as [| p1].
    + exfalso. simpl in Hp. apply not_prime_0; exact Hp.
    + destruct p1 as [| p2].
      * exfalso. simpl in Hp. apply not_prime_1; exact Hp.
      * destruct p2 as [| p3].
        { simpl. left. reflexivity. }
        { destruct p3 as [| p4].
          - simpl. right. left. reflexivity.
          - destruct p4 as [| p5].
            + exfalso. simpl in Hp. apply not_prime_4; exact Hp.
            + exfalso. lia.
        }
  - constructor.
    + constructor.
      * simpl. lia.
      * constructor.
    + constructor.
      * constructor.
      * constructor.
  - constructor.
    + simpl. intros [H|H]; [inversion H|contradiction].
    + constructor.
      * simpl. intros [].
      * constructor.
Qed.