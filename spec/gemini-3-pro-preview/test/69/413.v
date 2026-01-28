Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occ (l : list Z) (x : Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb h x then 1 else 0) + count_occ t x
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => count_occ l x >=? x) l in
  fold_right Z.max (-1) candidates.

Example test_search: search [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 9%Z; 18%Z; 8%Z; 9%Z; 10%Z; 10%Z; 10%Z; 10%Z; 10%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z] = 1%Z.
Proof.
  reflexivity.
Qed.