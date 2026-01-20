Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.
Open Scope Z_scope.

Fixpoint sum_squares_aux (i : nat) (lst : list Z) : Z :=
  match lst with
  | nil => 0%Z
  | x :: xs =>
      let term :=
        if Nat.eqb (Nat.modulo i 3) 0 then (x * x)%Z
        else if Nat.eqb (Nat.modulo i 4) 0 then ((x * x)%Z * x)%Z
        else x
      in (term + sum_squares_aux (S i) xs)%Z
  end.

Definition sum_squares_spec (lst : list Z) (ans : Z) : Prop :=
  ans = sum_squares_aux 0 lst.

Example test_sum_squares : sum_squares_spec [1; 2; 3] 6.
Proof.
  unfold sum_squares_spec.
  (* We can simply compute the result since all values are concrete *)
  simpl.
  (* 
     Trace:
     i=0: 0 mod 3 = 0 -> term = 1*1 = 1
     i=1: 1 mod 3 != 0, 1 mod 4 != 0 -> term = 2
     i=2: 2 mod 3 != 0, 2 mod 4 != 0 -> term = 3
     Sum: 1 + 2 + 3 = 6
  *)
  reflexivity.
Qed.