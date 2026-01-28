Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint count (l : list Z) (x : Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if h =? x then 1 else 0) + count t x
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => count l x >=? x) l in
  fold_left Z.max candidates (-1).

Example test_case: search [1%Z; 2%Z; 3%Z; 17%Z; 5%Z; 18%Z; 8%Z; 9%Z; 10%Z; 10%Z; 10%Z; 10%Z; 10%Z; 11%Z; 2%Z; 12%Z; 13%Z; 14%Z; 15%Z; 3%Z] = 2%Z.
Proof.
  reflexivity.
Qed.