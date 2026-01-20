Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  let fix aux (l : list Z) (current_sum max_sum : Z) : Z :=
    match l with
    | [] => max_sum
    | x :: xs =>
        let s := current_sum - x in
        let s := if s <? 0 then 0 else s in
        aux xs s (Z.max s max_sum)
    end in
  let max_s := aux nums 0 0 in
  if max_s =? 0 then
    match nums with
    | [] => 0
    | x :: xs => 
      let fix max_neg (l : list Z) (m : Z) : Z :=
        match l with
        | [] => m
        | y :: ys => max_neg ys (Z.max (-y) m)
        end in
      - (max_neg xs (-x))
    end
  else - max_s.

Example test_minSubArraySum: minSubArraySum [1; 1; -1; 1; -1; 1; -1; 1; 1; -1; 1; -1; -4; 1; -1] = -5.
Proof. reflexivity. Qed.