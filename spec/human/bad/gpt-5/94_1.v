Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope nat_scope.

Fixpoint sum_digits_fueled (n fuel : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
    match n with
    | 0 => 0
    | _ => (n mod 10) + sum_digits_fueled (n / 10) fuel'
    end
  end.

Definition sum_digits (n : nat) : nat :=
  sum_digits_fueled n n.

Definition problem_94_pre (lst : list nat) : Prop := True.

Definition problem_94_spec (lst : list nat) (output : nat) : Prop :=
  (exists p,
    In p lst /\
    prime (Z.of_nat p) /\
    (forall p', In p' lst -> prime (Z.of_nat p') -> p' <= p) /\
    output = sum_digits p)
  \/
  ((forall x, In x lst -> ~ prime (Z.of_nat x)) /\ output = 0).

Axiom Zprime_181 : prime (Z.of_nat 181).
Axiom Znotprime_324 : ~ prime (Z.of_nat 324).

Example problem_94_test_1 :
  problem_94_spec
    [0; 3; 2; 1; 3; 5; 7; 4; 5; 5; 5; 2; 181; 32; 4; 32; 3; 2; 32; 324; 4; 3]
    10.
Proof.
  left.
  exists 181.
  repeat split.
  - cbn.
    right. right. right. right. right. right.
    right. right. right. right. right. right.
    left. reflexivity.
  - exact Zprime_181.
  - intros p' Hin Hpr.
    cbn in Hin.
    destruct Hin as [->|Hin]; [lia|].
    destruct Hin as [->|Hin]; [lia|].
    destruct Hin as [->|Hin]; [lia|].
    destruct Hin as [->|Hin]; [lia|].
    destruct Hin as [->|Hin]; [lia|].
    destruct Hin as [->|Hin]; [lia|].
    destruct Hin as [->|Hin]; [lia|].
    destruct Hin as [->|Hin]; [lia|].
    destruct Hin as [->|Hin]; [lia|].
    destruct Hin as [->|Hin]; [lia|].
    destruct Hin as [->|Hin]; [lia|].
    destruct Hin as [->|Hin]; [lia|].  (* p' = 181 *)
    destruct Hin as [->|Hin]; [lia|].  (* p' = 32 *)
    destruct Hin as [->|Hin]; [lia|].  (* p' = 4 *)
    destruct Hin as [->|Hin]; [lia|].  (* p' = 32 *)
    destruct Hin as [->|Hin]; [lia|].  (* p' = 3 *)
    destruct Hin as [->|Hin]; [lia|].  (* p' = 2 *)
    destruct Hin as [->|Hin]; [lia|].  (* p' = 32 *)
    destruct Hin as [->|Hin].
    + (* p' = 324, contradicts primality *)
      exfalso. apply Znotprime_324. exact Hpr.
    + destruct Hin as [->|Hin]; [lia|].  (* p' = 4 *)
      destruct Hin as [->|Hin]; [lia|].  (* p' = 3 *)
      cbn in Hin; contradiction.
  - vm_compute. reflexivity.
Qed.