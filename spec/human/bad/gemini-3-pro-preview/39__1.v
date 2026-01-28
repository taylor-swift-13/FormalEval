Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.Lists.ListSet.
Require Import Lia.
Import ListNotations.


Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

(* IsFib 命题：一个数是斐波那契数。*)

(* 关系：fib_at i v 表示 v 是第 i 个斐波那契数 *)
Inductive fib_at : nat -> nat -> Prop :=
| fib_at_0 : fib_at 0 0
| fib_at_1 : fib_at 1 1
| fib_at_S : forall i a b,
    fib_at i a ->
    fib_at (S i) b ->
    fib_at (S (S i)) (a + b).

Definition IsFib (n : nat) : Prop := exists i : nat, fib_at i n.

(* IsPrimeFib 命题：一个数既是素数又是斐波那契数 *)
Definition IsPrimeFib (n : nat) : Prop :=
  IsPrime n /\ IsFib n.


(* Pre: n must be at least 1 to have a valid n-th prime-fibonacci number *)
Definition problem_39_pre (n : nat) : Prop := (n >= 1)%nat.

Definition problem_39_spec (n r : nat) : Prop :=
  IsPrimeFib r /\
  (exists (S : list nat),
    (* 1. 列表 S 的长度必须是 n-1 *)
    length S = n - 1 /\

    (* 2. 列表 S 中没有重复元素，使其能真正代表一个“集合” *)
    NoDup S /\

    (* 3. 列表 S 精确地包含了所有小于 r 的素斐波那契数 *)
    (forall y : nat, In y S <-> (y < r /\ IsPrimeFib y))
  ).

Example problem_39_test : problem_39_spec 1 2.
Proof.
  unfold problem_39_spec.
  split.
  - (* Part 1: Prove IsPrimeFib 2 *)
    split.
    + (* IsPrime 2 *)
      unfold IsPrime. split.
      * lia. (* 1 < 2 *)
      * intros d Hmod.
        destruct d as [| d'].
        { (* d = 0 *)
          (* In Coq, n mod 0 = n. So 2 mod 0 = 2. Hmod becomes 2 = 0. *)
          simpl in Hmod. discriminate. }
        destruct d' as [| d''].
        { (* d = 1 *) left. reflexivity. }
        destruct d'' as [| d'''].
        { (* d = 2 *) right. reflexivity. }
        { (* d >= 3 *)
          assert (Hgt: 2 < S (S (S d'''))) by lia.
          rewrite Nat.mod_small in Hmod; try lia.
          discriminate.
        }
    + (* IsFib 2 *)
      exists 3.
      replace 2 with (1 + 1) by lia.
      apply fib_at_S.
      * apply fib_at_1.
      * replace 1 with (0 + 1) by lia.
        apply fib_at_S.
        -- apply fib_at_0.
        -- apply fib_at_1.
  - (* Part 2: Existence of set S *)
    exists [].
    split.
    + (* length [] = 1 - 1 *)
      simpl. lia.
    + split.
      * (* NoDup [] *)
        apply NoDup_nil.
      * (* Elements check *)
        intros y. split.
        -- (* In y [] -> False *)
           intros H. inversion H.
        -- (* y < 2 /\ IsPrimeFib y -> In y [] *)
           intros [Hlt [Hprime Hfib]].
           unfold IsPrime in Hprime.
           destruct Hprime as [Hgt1 _].
           (* 1 < y < 2 is impossible in nat *)
           lia.
Qed.