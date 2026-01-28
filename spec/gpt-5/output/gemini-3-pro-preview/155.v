Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

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

Example test_even_odd_count : even_odd_count_spec 7%Z (0, 1).
Proof.
  (* Unfold the specification *)
  unfold even_odd_count_spec.
  
  (* Simplify Z arithmetic to get the natural number 7 *)
  simpl.
  
  (* We need to provide the list of digits for 7.
     Since 7 is a single digit, the list is [7]. *)
  exists (7 :: nil).
  
  (* Split the goal into proving digits10 holds and proving the result matches *)
  split.
  
  - (* Subgoal 1: Prove digits10 7 (7 :: nil) *)
    apply digits10_lt10.
    (* Prove 0 < 7 /\ 7 < 10 *)
    split.
    + (* 0 < 7 *)
      repeat constructor.
    + (* 7 < 10 *)
      repeat constructor.
    
  - (* Subgoal 2: Prove (0, 1) = (count_even [7], count_odd [7]) *)
    simpl.
    reflexivity.
Qed.