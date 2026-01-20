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

Example test_even_odd_11109 : even_odd_count_spec 11109%Z (1, 4).
Proof.
  unfold even_odd_count_spec.
  simpl.
  exists (1 :: 1 :: 1 :: 0 :: 9 :: nil).
  split.
  - assert (H1 : digits10 1 (1 :: nil)).
    { apply digits10_lt10; split; lia. }
    assert (H11 : digits10 11 (1 :: 1 :: nil)).
    { eapply digits10_step with (d := 1) (q := 1) (l := 1 :: nil).
      + lia.
      + reflexivity.
      + reflexivity.
      + exact H1. }
    assert (H111 : digits10 111 (1 :: 1 :: 1 :: nil)).
    { eapply digits10_step with (d := 1) (q := 11) (l := 1 :: 1 :: nil).
      + lia.
      + reflexivity.
      + reflexivity.
      + exact H11. }
    assert (H1110 : digits10 1110 (1 :: 1 :: 1 :: 0 :: nil)).
    { eapply digits10_step with (d := 0) (q := 111) (l := 1 :: 1 :: 1 :: nil).
      + lia.
      + reflexivity.
      + reflexivity.
      + exact H111. }
    eapply digits10_step with (d := 9) (q := 1110) (l := 1 :: 1 :: 1 :: 0 :: nil).
    + lia.
    + reflexivity.
    + reflexivity.
    + exact H1110.
  - simpl; reflexivity.
Qed.