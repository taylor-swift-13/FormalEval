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

Example problem_39_test_case : problem_39_spec 2 3.
Proof.
  unfold problem_39_spec.
  split.
  - (* Part 1: Prove IsPrimeFib 3 *)
    unfold IsPrimeFib. split.
    + (* IsPrime 3 *)
      unfold IsPrime. split.
      * (* 1 < 3 *)
        lia.
      * (* Divisors of 3 *)
        intros d Hmod.
        destruct d.
        { (* d = 0 *) simpl in Hmod. discriminate. }
        destruct d.
        { (* d = 1 *) left. reflexivity. }
        destruct d.
        { (* d = 2 *) simpl in Hmod. discriminate. }
        destruct d.
        { (* d = 3 *) right. reflexivity. }
        { (* d >= 4 *)
          assert (Hgt: 3 < S (S (S (S d)))) by lia.
          apply Nat.mod_small in Hgt.
          rewrite Hgt in Hmod.
          discriminate.
        }
    + (* IsFib 3 *)
      unfold IsFib.
      exists 4.
      simpl. reflexivity.
  
  - (* Part 2: Prove the set property *)
    (* n=2, n-1=1. We need a list of length 1 containing PrimeFib numbers < 3. That is [2]. *)
    exists [2].
    split.
    + (* length [2] = 2 - 1 *)
      simpl. reflexivity.
    + split.
      * (* NoDup [2] *)
        constructor.
        { intro H. inversion H. }
        { constructor. }
      * (* Elements check *)
        intros y. split.
        { (* In y [2] -> ... *)
          intro H.
          destruct H as [H | H].
          - (* y = 2 *)
            subst. split.
            + lia.
            + (* IsPrimeFib 2 *)
              unfold IsPrimeFib. split.
              * unfold IsPrime. split.
                { lia. }
                { intros d Hmod.
                  destruct d. { simpl in Hmod. discriminate. }
                  destruct d. { left. reflexivity. }
                  destruct d. { right. reflexivity. }
                  { assert (Hgt: 2 < S (S (S d))) by lia.
                    apply Nat.mod_small in Hgt.
                    rewrite Hgt in Hmod. discriminate. }
                }
              * unfold IsFib. exists 3. simpl. reflexivity.
          - inversion H.
        }
        { (* ... -> In y [2] *)
          intro H.
          destruct H as [Hlt Hpf].
          unfold IsPrimeFib in Hpf.
          destruct Hpf as [Hp _].
          unfold IsPrime in Hp.
          destruct Hp as [Hgt _].
          (* 1 < y < 3 -> y = 2 *)
          assert (y = 2) by lia.
          subst.
          left. reflexivity.
        }
Qed.