Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.
Require Import Lia.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => 1
  | S k => (S k) * factorial k
  end.

Fixpoint sum_upto (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => sum_upto k + S k
  end.

Definition f_spec (n : nat) (ans : list nat) : Prop :=
  length ans = n /\
  forall i, 1 <= i <= n ->
    nth_error ans (i - 1) = Some (if Nat.even i then factorial i else sum_upto i).

Example test_f_spec : f_spec 5 (1 :: 2 :: 6 :: 24 :: 15 :: nil).
Proof.
  unfold f_spec.
  split.
  - simpl. reflexivity.
  - intros i [H1 H2].
    destruct i as [|i'].
    + lia.
    + destruct i' as [|i''].
      * simpl. reflexivity.
      * destruct i'' as [|i'''].
        -- simpl. reflexivity.
        -- destruct i''' as [|i''''].
           ++ simpl. reflexivity.
           ++ destruct i'''' as [|i'''''].
              ** simpl. reflexivity.
              ** destruct i''''' as [|i''''''].
                 --- simpl. reflexivity.
                 --- lia.
Qed.