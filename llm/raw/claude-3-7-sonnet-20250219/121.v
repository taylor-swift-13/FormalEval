
Require Import List.
Import ListNotations.
Require Import Nat.
Require Import ZArith.
Open Scope Z_scope.

Fixpoint sum_odd_even_pos (lst : list Z) : Z :=
  match lst with
  | [] => 0
  | x :: xs =>
    let rest := sum_odd_even_pos (tl xs) in
    if Z.odd x && Z.even 0 then x + rest else rest
  end.

Definition solution_spec (lst : list Z) (res : Z) : Prop :=
  res = 
    fold_left (fun acc '(i, v) =>
                 if (Nat.even i) && (Z.odd v) then acc + v else acc)
              (combine (seq 0 (length lst)) lst) 0.
