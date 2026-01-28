Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occ (n : Z) (l : list Z) : Z :=
  fold_right (fun x acc => if Z.eqb x n then acc + 1 else acc) 0 l.

Definition solve (l : list Z) : list Z :=
  let evens := filter Z.even l in
  let unique_evens := nodup Z.eq_dec evens in
  let counts := map (fun x => (x, count_occ x evens)) unique_evens in
  let better (p1 p2 : Z * Z) :=
    let (v1, c1) := p1 in
    let (v2, c2) := p2 in
    if c1 >? c2 then p1
    else if c1 <? c2 then p2
    else if v1 <? v2 then p1 else p2
  in
  match counts with
  | [] => []
  | h :: t => 
      let (v, c) := fold_left better t h in
      [v; c]
  end.

Example test_case_new : solve [1; 1; 1; 1; 1; 2; 1; 2; 2; 2; 2] = [2; 5].
Proof. reflexivity. Qed.