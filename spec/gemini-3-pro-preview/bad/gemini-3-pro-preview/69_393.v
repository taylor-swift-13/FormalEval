Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition count (v : Z) (l : list Z) : Z :=
  fold_right (fun x acc => if x =? v then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  fold_left (fun acc x => 
    let freq := count x l in
    if (freq >=? x) && (x >? acc) then x else acc
  ) l (-1).

Example test_case: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 12%Z; 4%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 6%Z; 6%Z; 6%Z; 12%Z; 7%Z; 8%Z; 8%Z; 9%Z; 9%Z; 10%Z; 10%Z; 11%Z; 11%Z; 12%Z; 13%Z; 5%Z] = 4%Z.
Proof.
  compute.
  reflexivity.
Qed.