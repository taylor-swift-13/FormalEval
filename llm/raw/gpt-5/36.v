Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Import ListNotations.

Fixpoint digits10 (n : nat) : list nat :=
  if n <? 10 then [n] else (n mod 10) :: digits10 (n / 10).

Fixpoint count_sevens_digits (ds : list nat) : nat :=
  match ds with
  | [] => 0
  | d :: ds' => (if Nat.eqb d 7 then 1 else 0) + count_sevens_digits ds'
  end.

Definition count_sevens_in_nat (i : nat) : nat :=
  count_sevens_digits (digits10 i).

Definition div11_or_13 (i : nat) : bool :=
  (i mod 11 =? 0) || (i mod 13 =? 0).

Fixpoint sum_upto (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => sum_upto f n' + f n'
  end.

Definition fizz_buzz_spec (n : nat) (cnt : nat) : Prop :=
  cnt = sum_upto (fun i => if div11_or_13 i then count_sevens_in_nat i else 0) n.