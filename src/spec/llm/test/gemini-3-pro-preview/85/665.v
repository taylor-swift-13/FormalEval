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

Example test_add_sum : add_spec [2; 4; 7; 17; 10; 8; 10; 12; 14; 42; 18; 20; 17; 24; 26; 28; 30] 138.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.