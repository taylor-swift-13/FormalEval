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

Example test_add_sum : add_spec [3; 28; 5; 7; 9; 2; 122; 6; 8; 10; 556; 3; 100; 187; 920; 42; 37; 29; 2] 88.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.