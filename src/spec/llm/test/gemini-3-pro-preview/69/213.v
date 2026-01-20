Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint count (l : list Z) (x : Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb h x then 1 else 0) + count t x
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => x <=? count l x) l in
  match candidates with
  | [] => -1
  | _ => fold_right Z.max (-1) candidates
  end.

Example test_case: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 4%Z; 4%Z; 9%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 6%Z; 7%Z; 7%Z; 7%Z; 8%Z; 8%Z; 8%Z; 9%Z; 9%Z; 9%Z; 10%Z; 10%Z; 10%Z; 5%Z; 1%Z; 3%Z] = 3%Z.
Proof. reflexivity. Qed.