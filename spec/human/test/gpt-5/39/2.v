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

Example problem_39_pre_2 : problem_39_pre 2.
Proof.
  unfold problem_39_pre. lia.
Qed.

Example problem_39_spec_2_3 : problem_39_spec 2 3.
Proof.
  unfold problem_39_spec.
  split.
  - unfold IsPrimeFib.
    split.
    + unfold IsPrime.
      split.
      * lia.
      * intros d Hd.
        destruct d as [| d1].
        -- simpl in Hd. lia.
        -- destruct d1 as [| d2].
           ++ left. reflexivity.
           ++ destruct d2 as [| d3].
              ** simpl in Hd. lia.
              ** destruct d3 as [| d4].
                 *** right. reflexivity.
                 *** assert (Hlt : 3 < S (S (S (S d4)))) by lia.
                     rewrite (Nat.mod_small 3 (S (S (S (S d4)))) Hlt) in Hd.
                     lia.
    + unfold IsFib.
      exists 4.
      simpl. reflexivity.
  - exists [2].
    split.
    + simpl. lia.
    + split.
      * constructor.
        -- simpl. intros H. inversion H.
        -- constructor.
      * intros y. split.
        -- intros Hy.
           simpl in Hy.
           destruct Hy as [Hy|Hy].
           ++ subst.
              split.
              ** lia.
              ** unfold IsPrimeFib.
                 split.
                 --- unfold IsPrime.
                     split.
                     +++ lia.
                     +++ intros d Hd.
                         destruct d as [| d1].
                         *** simpl in Hd. lia.
                         *** destruct d1 as [| d2].
                             **** left. reflexivity.
                             **** destruct d2 as [| d3].
                                  ***** right. reflexivity.
                                  ***** assert (Hlt : 2 < S (S (S d3))) by lia.
                                        rewrite (Nat.mod_small 2 (S (S (S d3))) Hlt) in Hd.
                                        lia.
                 --- unfold IsFib.
                     exists 3.
                     simpl. reflexivity.
           ++ inversion Hy.
        -- intros [Hylt HyPF].
           destruct y as [| y1].
           ++ exfalso.
              destruct HyPF as [HyPrime _].
              destruct HyPrime as [Hlt1 _].
              lia.
           ++ destruct y1 as [| y2].
              ** exfalso.
                 destruct HyPF as [HyPrime _].
                 destruct HyPrime as [Hlt1 _].
                 lia.
              ** assert (y2 = 0) by lia.
                 subst y2.
                 simpl. left. reflexivity.
Qed.