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

Example test_even_odd_2369 : even_odd_count_spec 2369%Z (2, 2).
Proof.
  unfold even_odd_count_spec.
  simpl.
  exists (2 :: 3 :: 6 :: 9 :: nil).
  split.
  - assert (Hmod2369 : Nat.modulo 2369 10 = 9) by (vm_compute; reflexivity).
    assert (Hdiv2369 : Nat.div 2369 10 = 236) by (vm_compute; reflexivity).
    assert (Hmod236 : Nat.modulo 236 10 = 6) by (vm_compute; reflexivity).
    assert (Hdiv236 : Nat.div 236 10 = 23) by (vm_compute; reflexivity).
    assert (Hmod23 : Nat.modulo 23 10 = 3) by (vm_compute; reflexivity).
    assert (Hdiv23 : Nat.div 23 10 = 2) by (vm_compute; reflexivity).
    eapply (digits10_step 2369 (2 :: 3 :: 6 :: nil) 9 236).
    + lia.
    + rewrite Hmod2369. reflexivity.
    + rewrite Hdiv2369. reflexivity.
    + eapply (digits10_step 236 (2 :: 3 :: nil) 6 23).
      * lia.
      * rewrite Hmod236. reflexivity.
      * rewrite Hdiv236. reflexivity.
      * eapply (digits10_step 23 (2 :: nil) 3 2).
        -- lia.
        -- rewrite Hmod23. reflexivity.
        -- rewrite Hdiv23. reflexivity.
        -- apply digits10_lt10; split; lia.
  - simpl. reflexivity.
Qed.