
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition sum_squares_spec (lst : list Z) (res : Z) : Prop :=
  res = 
    let fix aux (l : list Z) (i : nat) : Z :=
      match l with
      | [] => 0
      | x :: xs =>
        if Nat.modulo i 3 =? 0 then x * x + aux xs (S i)
        else if Nat.modulo i 4 =? 0 then x * x * x + aux xs (S i)
        else x + aux xs (S i)
      end
    in aux lst 0.
