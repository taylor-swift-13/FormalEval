Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  let step (acc : Z * Z) (x : Z) :=
    let (s, max_s) := acc in
    let s' := s - x in
    let s'' := if s' <? 0 then 0 else s' in
    (s'', Z.max max_s s'')
  in
  let (final_s, max_sum) := fold_left step nums (0, 0) in
  if max_sum =? 0 then
    match nums with
    | [] => 0
    | x :: xs => - (fold_left Z.max (map Z.opp xs) (-x))
    end
  else
    - max_sum.

Example test_minSubArraySum: minSubArraySum [2%Z; 1%Z; -3%Z; 4%Z; -1%Z; 2%Z; 1%Z; -5%Z; 4%Z] = -5%Z.
Proof.
  compute. reflexivity.
Qed.