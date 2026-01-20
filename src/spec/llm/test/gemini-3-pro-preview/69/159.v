Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (l : list Z) (n : Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eq_dec h n then 1 else 0) + count t n
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => Z.eqb x (count l x)) l in
  fold_right Z.max (-1) candidates.

Example test_search: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 1%Z; 14%Z; 2%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 1%Z] = 3%Z.
Proof. reflexivity. Qed.