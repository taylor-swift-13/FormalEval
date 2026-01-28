Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  let neg_nums := map Z.opp nums in
  let fix kadane (l : list Z) (current : Z) (best : Z) : Z :=
    match l with
    | [] => best
    | x :: xs =>
        let current' := current + x in
        let current'' := if current' <? 0 then 0 else current' in
        let best' := if best <? current'' then current'' else best in
        kadane xs current'' best'
    end in
  let max_sum := kadane neg_nums 0 0 in
  if max_sum =? 0 then
    let fix max_elem (l : list Z) (m : Z) : Z :=
      match l with
      | [] => m
      | x :: xs => max_elem xs (if m <? x then x else m)
      end in
    match neg_nums with
    | [] => 0 
    | x :: xs => Z.opp (max_elem xs x)
    end
  else
    Z.opp max_sum.

Example test_minSubArraySum: minSubArraySum [2; 1; -3; -1; 2; 1; -5; 5] = -6.
Proof. reflexivity. Qed.