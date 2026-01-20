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

Example test_even_odd_neg2468 : even_odd_count_spec (-2468)%Z (4, 0).
Proof.
  unfold even_odd_count_spec.
  simpl.
  exists (2 :: 4 :: 6 :: 8 :: nil).
  split.
  - assert (H2: digits10 2 (2 :: nil)).
    { apply digits10_lt10; split; lia. }
    assert (H24: digits10 24 (2 :: 4 :: nil)).
    { eapply digits10_step with (n := 24) (l := 2 :: nil) (d := Nat.modulo 24 10) (q := Nat.div 24 10).
      all: try lia.
      all: try reflexivity.
      exact H2.
    }
    assert (H246: digits10 246 (2 :: 4 :: 6 :: nil)).
    { eapply digits10_step with (n := 246) (l := 2 :: 4 :: nil) (d := Nat.modulo 246 10) (q := Nat.div 246 10).
      all: try lia.
      all: try reflexivity.
      exact H24.
    }
    eapply digits10_step with (n := 2468) (l := 2 :: 4 :: 6 :: nil) (d := Nat.modulo 2468 10) (q := Nat.div 2468 10).
    all: try lia.
    all: try reflexivity.
    exact H246.
  - simpl; reflexivity.
Qed.