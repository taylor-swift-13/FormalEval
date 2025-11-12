
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.
Open Scope Z_scope.
Open Scope nat_scope.

Fixpoint sumZ (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => x + sumZ xs
  end.

Definition subarray_sum (l : list Z) (i k : nat) : Z :=
  sumZ (firstn k (skipn i l)).

Definition minSubArraySum_spec (nums : list Z) (ans : Z) : Prop :=
  (exists i k, 0 < k /\ i + k <= length nums /\ ans = subarray_sum nums i k) /\
  (forall i k, 0 < k -> i + k <= length nums -> ans <= subarray_sum nums i k).
