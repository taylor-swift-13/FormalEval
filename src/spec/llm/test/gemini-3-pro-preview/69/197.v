Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (l : list Z) (n : Z) : Z :=
  match l with
  | [] => 0
  | h :: t => if Z.eqb h n then 1 + count t n else count t n
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => Z.geb (count l x) x) l in
  fold_right Z.max (-1) candidates.

Example test_case: search [1%Z; 2%Z; 3%Z; 5%Z; 6%Z; 18%Z; 7%Z; 8%Z; 9%Z; 10%Z; 10%Z; 10%Z; 10%Z; 10%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z] = 1%Z.
Proof. reflexivity. Qed.