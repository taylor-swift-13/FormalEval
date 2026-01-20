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

Example test_even_odd_neg_2216 : even_odd_count_spec (-2216%Z) (3, 1).
Proof.
  unfold even_odd_count_spec.
  simpl.
  exists (2 :: 2 :: 1 :: 6 :: nil).
  split.
  - assert (H2 : digits10 2 (2 :: nil)).
    { apply digits10_lt10; split; lia. }
    assert (H22 : digits10 22 (2 :: 2 :: nil)).
    { eapply digits10_step with (l := (2 :: nil)) (d := 2) (q := 2).
      - lia.
      - simpl; reflexivity.
      - simpl; reflexivity.
      - exact H2. }
    assert (H221 : digits10 221 (2 :: 2 :: 1 :: nil)).
    { eapply digits10_step with (l := (2 :: 2 :: nil)) (d := 1) (q := 22).
      - lia.
      - simpl; reflexivity.
      - simpl; reflexivity.
      - exact H22. }
    eapply digits10_step with (l := (2 :: 2 :: 1 :: nil)) (d := 6) (q := 221).
    + lia.
    + simpl; reflexivity.
    + simpl; reflexivity.
    + exact H221.
  - simpl; reflexivity.
Qed.