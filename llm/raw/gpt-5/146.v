Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.

Definition pow10z (k : nat) : Z := Z.of_nat (Nat.pow 10 k).

Definition first_digit_odd (z : Z) : Prop :=
  exists k d r,
    1 <= Z.of_nat k /\
    1 <= d /\ d <= 9 /\
    pow10z k <= z /\ z < pow10z (S k) /\
    0 <= r /\ r < pow10z k /\
    z = d * pow10z k + r /\
    Z.odd d = true.

Definition specialFilter_pred (z : Z) : Prop :=
  z > 10 /\ first_digit_odd z /\ Z.odd z = true.

Inductive count_specialFilter : list Z -> nat -> Prop :=
| cs_nil : count_specialFilter [] 0
| cs_cons_true : forall x xs m,
    count_specialFilter xs m ->
    specialFilter_pred x ->
    count_specialFilter (x :: xs) (S m)
| cs_cons_false : forall x xs m,
    count_specialFilter xs m ->
    ~ specialFilter_pred x ->
    count_specialFilter (x :: xs) m.

Definition specialFilter_spec (nums : list Z) (ans : Z) : Prop :=
  exists n, count_specialFilter nums n /\ ans = Z.of_nat n.