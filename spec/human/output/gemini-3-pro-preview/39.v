Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.Lists.ListSet.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

(* fib i returns the i-th Fibonacci number *)
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

Example problem_39_test_case : problem_39_spec 1 2.
Proof.
  unfold problem_39_spec.
  split.
  - (* Part 1: Prove IsPrimeFib 2 *)
    unfold IsPrimeFib. split.
    + (* IsPrime 2 *)
      unfold IsPrime. split.
      * (* 1 < 2 *)
        lia.
      * (* Divisors of 2 *)
        intros d Hmod.
        destruct d.
        { (* d = 0 *)
          (* In Coq nat, x mod 0 = x. So 2 mod 0 = 2. 2 = 0 is False. *)
          simpl in Hmod. discriminate. 
        }
        destruct d.
        { (* d = 1 *) left. reflexivity. }
        destruct d.
        { (* d = 2 *) right. reflexivity. }
        { (* d >= 3 *)
          (* If d > 2, 2 mod d = 2. *)
          assert (Hgt: 2 < S (S (S d))) by lia.
          apply Nat.mod_small in Hgt.
          rewrite Hgt in Hmod.
          discriminate.
        }
    + (* IsFib 2 *)
      unfold IsFib.
      exists 3.
      simpl. reflexivity.
  
  - (* Part 2: Prove the set property *)
    (* Since n=1, n-1=0. We need an empty list representing numbers < 2 that are PrimeFib. *)
    exists [].
    split.
    + (* length [] = 1 - 1 *)
      simpl. reflexivity.
    + split.
      * (* NoDup [] *)
        constructor.
      * (* Elements check *)
        intros y. split.
        { (* In y [] -> ... *)
          intro H. inversion H.
        }
        { (* ... -> In y [] *)
          intro H.
          destruct H as [Hlt Hpf].
          unfold IsPrimeFib in Hpf.
          destruct Hpf as [Hp _].
          unfold IsPrime in Hp.
          destruct Hp as [Hgt _].
          (* We have y < 2 and 1 < y. No natural number satisfies this. *)
          lia.
        }
Qed.