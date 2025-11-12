
Require Import List.
Require Import ZArith.

Open Scope Z_scope.

Definition largest_smallest_integers_spec (lst : list Z) (result : option Z * option Z) : Prop :=
  let neg := filter (fun x => x <? 0) lst in
  let pos := filter (fun x => 0 <? x) lst in
  result = (if neg = [] then None else Some (fold_left Z.max neg (hd 0 neg)),
            if pos = [] then None else Some (fold_left Z.min pos (hd 0 pos))).
