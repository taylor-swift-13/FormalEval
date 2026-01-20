
Require Import ZArith.
Open Scope Z_scope.

Definition rounded_avg_spec (n m : Z) (res : option Z) : Prop :=
  if Z_gt_dec n m then
    res = None
  else
    let avg := Z.round ( (n + m) / 2 ) in
    (* Since Coq does not have a built-in round for Z, define rounding as follows: 
       rounding to nearest integer for (n+m)/2, where (n+m) is Z and division is Z-based *)
    let sum := n + m in
    let half := sum / 2 in
    let rem := sum mod 2 in
    (* If remainder is 1 or -1, round up; else round down *)
    let rounded_avg :=
      if Z.abs rem * 2 >= 1 then
        if sum >= 0 then half + 1 else half - 1
      else half
    in
    res = Some rounded_avg.
