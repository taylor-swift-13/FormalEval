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

Example test_sum_squares_case :
  sum_squares_spec [-12%Z; -17%Z; 20%Z; 33%Z; 37%Z; 40%Z; 45%Z; 48%Z; 49%Z; 50%Z; 58%Z; 70%Z; 64%Z; 72%Z; 80%Z; 82%Z; 88%Z; 92%Z; 94%Z; 50%Z; 37%Z] 926354%Z.
Proof.
  unfold sum_squares_spec.
  simpl.
  reflexivity.
Qed.