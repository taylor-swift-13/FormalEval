Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.

Fixpoint count_even (l : list nat) : nat :=
  match l with
  | nil => 0
  | d :: t => if Nat.even d then S (count_even t) else count_even t
  end.

Fixpoint count_odd (l : list nat) : nat :=
  match l with
  | nil => 0
  | d :: t => if Nat.odd d then S (count_odd t) else count_odd t
  end.

Inductive digits10 : nat -> list nat -> Prop :=
| digits10_zero : digits10 0 (0 :: nil)
| digits10_lt10 : forall k, 0 < k /\ k < 10 -> digits10 k (k :: nil)
| digits10_step : forall n l d q,
    10 <= n ->
    d = Nat.modulo n 10 ->
    q = Nat.div n 10 ->
    digits10 q l ->
    digits10 n (List.app l (d :: nil)).

Definition even_odd_count_spec (num : Z) (res : nat * nat) : Prop :=
  let n := Z.to_nat (Z.abs num) in
  exists digits,
    digits10 n digits /\ res = (count_even digits, count_odd digits).

Example test_even_odd_6 : even_odd_count_spec 6%Z (1, 0).
Proof.
  unfold even_odd_count_spec.
  simpl.
  exists (6 :: nil).
  split.
  - apply digits10_lt10; split; lia.
  - simpl; reflexivity.
Qed.