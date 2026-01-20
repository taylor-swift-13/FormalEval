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

Example test_add_sum : add_spec [3; 1; 2; 3; 4; 5; 6; 7; 17; 8; 9; 10; 10; 12; 13; 14; 15; 16; 99; 18; 19; 20; 3; 3] 98.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.