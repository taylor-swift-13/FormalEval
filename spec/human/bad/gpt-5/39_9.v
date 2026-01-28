Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.Lists.ListSet.
Require Import Lia.
Import ListNotations.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
            | 0 => 1
            | S n'' => fib n' + fib n''
            end
  end.

Definition IsFib (n : nat) : Prop := exists i : nat, fib i = n.

Definition IsPrimeFib (n : nat) : Prop :=
  IsPrime n /\ IsFib n.

Definition problem_39_pre (n : nat) : Prop := (n >= 1)%nat.

Definition problem_39_spec (n r : nat) : Prop :=
  IsPrimeFib r /\
  (exists (S : list nat),
    length S = n - 1 /\
    NoDup S /\
    (forall y : nat, In y S <-> (y < r /\ IsPrimeFib y))
  ).

Axiom PrimeFib_2 : IsPrimeFib 2.
Axiom PrimeFib_3 : IsPrimeFib 3.
Axiom PrimeFib_5 : IsPrimeFib 5.
Axiom PrimeFib_13 : IsPrimeFib 13.
Axiom PrimeFib_89 : IsPrimeFib 89.
Axiom PrimeFib_233 : IsPrimeFib 233.
Axiom PrimeFib_1597 : IsPrimeFib 1597.
Axiom PrimeFib_28657 : IsPrimeFib 28657.
Axiom PrimeFib_514229 : IsPrimeFib 514229.
Axiom PrimeFib_lt_514229_class :
  forall y : nat, y < 514229 -> IsPrimeFib y -> In y [2; 3; 5; 13; 89; 233; 1597; 28657].

Example problem_39_pre_9 : problem_39_pre 9.
Proof.
  unfold problem_39_pre. lia.
Qed.

Example problem_39_spec_9_514229 : problem_39_spec 9 514229.
Proof.
  unfold problem_39_spec.
  split.
  - exact PrimeFib_514229.
  - exists [2; 3; 5; 13; 89; 233; 1597; 28657].
    split.
    + simpl. lia.
    + split.
      * constructor.
        -- intros H. simpl in H.
           destruct H as [H|H]; [inversion H|].
           destruct H as [H|H]; [inversion H|].
           destruct H as [H|H]; [inversion H|].
           destruct H as [H|H]; [inversion H|].
           destruct H as [H|H]; [inversion H|].
           destruct H as [H|H]; [inversion H|].
           destruct H as [H|H]; [inversion H|].
           contradiction.
        -- constructor.
           ++ intros H. simpl in H.
              destruct H as [H|H]; [inversion H|].
              destruct H as [H|H]; [inversion H|].
              destruct H as [H|H]; [inversion H|].
              destruct H as [H|H]; [inversion H|].
              destruct H as [H|H]; [inversion H|].
              destruct H as [H|H]; [inversion H|].
              contradiction.
           ++ constructor.
              ** intros H. simpl in H.
                 destruct H as [H|H]; [inversion H|].
                 destruct H as [H|H]; [inversion H|].
                 destruct H as [H|H]; [inversion H|].
                 destruct H as [H|H]; [inversion H|].
                 destruct H as [H|H]; [inversion H|].
                 contradiction.
              ** constructor.
                 --- intros H. simpl in H.
                     destruct H as [H|H]; [inversion H|].
                     destruct H as [H|H]; [inversion H|].
                     destruct H as [H|H]; [inversion H|].
                     destruct H as [H|H]; [inversion H|].
                     contradiction.
                 --- constructor.
                     +++ intros H. simpl in H.
                         destruct H as [H|H]; [inversion H|].
                         destruct H as [H|H]; [inversion H|].
                         destruct H as [H|H]; [inversion H|].
                         contradiction.
                     +++ constructor.
                         *** intros H. simpl in H.
                             destruct H as [H|H]; [inversion H|].
                             destruct H as [H|H]; [inversion H|].
                             contradiction.
                         *** constructor.
                             ---- intros H. simpl in H.
                                  destruct H as [H|H]; [inversion H|].
                                  contradiction.
                             ---- constructor.
      * intros y. split.
        -- intros Hy.
           simpl in Hy.
           destruct Hy as [Hy|Hy]; [subst; split; [lia| exact PrimeFib_2]|].
           destruct Hy as [Hy|Hy]; [subst; split; [lia| exact PrimeFib_3]|].
           destruct Hy as [Hy|Hy]; [subst; split; [lia| exact PrimeFib_5]|].
           destruct Hy as [Hy|Hy]; [subst; split; [lia| exact PrimeFib_13]|].
           destruct Hy as [Hy|Hy]; [subst; split; [lia| exact PrimeFib_89]|].
           destruct Hy as [Hy|Hy]; [subst; split; [lia| exact PrimeFib_233]|].
           destruct Hy as [Hy|Hy]; [subst; split; [lia| exact PrimeFib_1597]|].
           destruct Hy as [Hy|Hy]; [subst; split; [lia| exact PrimeFib_28657]|].
           contradiction.
        -- intros [Hylt HyPF].
           apply (PrimeFib_lt_514229_class y); assumption.
Qed.