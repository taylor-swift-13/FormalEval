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

Example test_add_sum : add_spec [11%Z; 22%Z; 101%Z; 10%Z; 44%Z; 55%Z; 88%Z; 21%Z; 7%Z; 77%Z; 88%Z; 100%Z; 7%Z] 132%Z.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.