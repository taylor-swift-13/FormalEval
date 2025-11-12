
Require Import List.
Require Import ZArith.

Open Scope Z_scope.

Definition sum_squares_spec (lst : list Z) (sum : Z) : Prop :=
  sum = fold_left Z.add
    (map (fun '(i, num) =>
      if Z.eqb (i mod 3) 0 then num ^ 2
      else if Z.eqb (i mod 4) 0 then num ^ 3
      else num)
    (combine (seq 0 (length lst)) lst)) 0.
