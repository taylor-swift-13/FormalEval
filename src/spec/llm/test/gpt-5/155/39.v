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

Example test_even_odd_2367 : even_odd_count_spec 2367%Z (2, 2).
Proof.
  unfold even_odd_count_spec.
  simpl.
  exists (2 :: 3 :: 6 :: 7 :: nil).
  split.
  - assert (H2 : digits10 2 (2 :: nil)).
    { apply digits10_lt10; split; lia. }
    assert (H23 : digits10 23 (2 :: 3 :: nil)).
    { eapply digits10_step with (n := 23) (l := 2 :: nil) (d := 3) (q := 2).
      - lia.
      - vm_compute; reflexivity.
      - vm_compute; reflexivity.
      - exact H2. }
    assert (H236 : digits10 236 (2 :: 3 :: 6 :: nil)).
    { eapply digits10_step with (n := 236) (l := 2 :: 3 :: nil) (d := 6) (q := 23).
      - lia.
      - vm_compute; reflexivity.
      - vm_compute; reflexivity.
      - exact H23. }
    eapply digits10_step with (n := 2367) (l := 2 :: 3 :: 6 :: nil) (d := 7) (q := 236).
    + lia.
    + vm_compute; reflexivity.
    + vm_compute; reflexivity.
    + exact H236.
  - simpl; reflexivity.
Qed.