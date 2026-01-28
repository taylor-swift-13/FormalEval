Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.Lists.ListSet.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Inductive fib_at : nat -> nat -> Prop :=
| fib_at_0 : fib_at 0 0
| fib_at_1 : fib_at 1 1
| fib_at_S : forall i a b,
    fib_at i a ->
    fib_at (S i) b ->
    fib_at (S (S i)) (a + b).

Definition IsFib (n : nat) : Prop := exists i : nat, fib_at i n.

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

Example prime_fib_test_1_pre : problem_39_pre 2.
Proof.
  unfold problem_39_pre; lia.
Qed.

Example prime_fib_test_1_spec : problem_39_spec 2 3.
Proof.
  unfold problem_39_spec.
  split.
  - unfold IsPrimeFib.
    split.
    + unfold IsPrime.
      split; [lia|].
      intros d Hd.
      destruct d as [|d'].
      * simpl in Hd. discriminate.
      * destruct d' as [|d''].
        -- left; reflexivity.
        -- destruct d'' as [|d'''].
           ++ simpl in Hd. discriminate.
           ++ destruct d''' as [|k].
              ** right; reflexivity.
              ** exfalso.
                 assert (3 < S (S (S (S k)))) by lia.
                 rewrite (Nat.mod_small 3 (S (S (S (S k))))) in Hd by lia.
                 discriminate.
    + unfold IsFib.
      exists 4.
      assert (fib_at 2 1).
      { apply fib_at_S with (i:=0) (a:=0) (b:=1); [apply fib_at_0|apply fib_at_1]. }
      assert (fib_at 3 2).
      { apply fib_at_S with (i:=1) (a:=1) (b:=1); [apply fib_at_1|assumption]. }
      assert (fib_at 4 3).
      { apply fib_at_S with (i:=2) (a:=1) (b:=2); [assumption|assumption]. }
      assumption.
  - exists [2].
    split.
    + simpl. lia.
    + split.
      * constructor.
        -- intros Hin. simpl in Hin. contradiction.
        -- constructor.
      * intros y. split.
        -- simpl. intros [Hy | Hin']; [subst y|contradiction].
           split; [lia|].
           unfold IsPrimeFib.
           split.
           ++ unfold IsPrime.
              split; [lia|].
              intros d Hd.
              destruct d as [|d'].
              ** simpl in Hd. discriminate.
              ** destruct d' as [|d''].
                 --- left; reflexivity.
                 --- destruct d'' as [|k].
                     ---- right; reflexivity.
                     ---- exfalso.
                          assert (2 < S (S (S k))) by lia.
                          rewrite (Nat.mod_small 2 (S (S (S k)))) in Hd by lia.
                          discriminate.
           ++ unfold IsFib.
              exists 3.
              assert (fib_at 2 1).
              { apply fib_at_S with (i:=0) (a:=0) (b:=1); [apply fib_at_0|apply fib_at_1]. }
              assert (fib_at 3 2).
              { apply fib_at_S with (i:=1) (a:=1) (b:=1); [apply fib_at_1|assumption]. }
              assumption.
        -- intros [Hylt HyPF]. simpl.
           destruct y as [|y'].
           ++ destruct HyPF as [HyPrime _]. destruct HyPrime as [Hgt1 _]. lia.
           ++ destruct y' as [|y''].
              ** destruct HyPF as [HyPrime _]. destruct HyPrime as [Hgt1 _]. lia.
              ** destruct y'' as [|y'''].
                 --- left; reflexivity.
                 --- lia.
Qed.