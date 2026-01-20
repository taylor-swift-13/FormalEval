Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint add_sum (lst : list Z) (is_odd_idx : bool) : Z :=
  match lst with
  | [] => 0
  | x :: xs => 
      (if is_odd_idx && Z.even x then x else 0) + add_sum xs (negb is_odd_idx)
  end.

Definition add_spec (lst : list Z) (res : Z) : Prop :=
  res = add_sum lst false.

Example test_add_sum : add_spec [1; 55; 2; 55; 3; 4; 5; 42; 7; 1; 9; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 20; 78; 78] 196.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.