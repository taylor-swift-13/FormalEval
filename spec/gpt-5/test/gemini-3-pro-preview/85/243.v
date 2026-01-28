Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Import ListNotations.
Open Scope Z_scope.

Fixpoint sum_even_at_odd_from (i : nat) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs =>
      let rest := sum_even_at_odd_from (S i) xs in
      if (Nat.odd i) && (Z.even x) then x + rest else rest
  end.

Definition sum_even_at_odd (l : list Z) : Z :=
  sum_even_at_odd_from 0 l.

Definition add_spec (lst : list Z) (s : Z) : Prop :=
  s = sum_even_at_odd lst.

Example test_case : add_spec [3%Z; 5%Z; 7%Z; 9%Z; 2%Z; 122%Z; 6%Z; 8%Z; 10%Z; 556%Z; 100%Z; 66%Z; 187%Z; 920%Z; 42%Z; 37%Z; 66%Z; 10%Z; 9%Z] 1682%Z.
Proof.
  unfold add_spec.
  unfold sum_even_at_odd.
  simpl.
  reflexivity.
Qed.