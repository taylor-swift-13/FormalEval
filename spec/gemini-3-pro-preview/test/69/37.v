Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occurrences (l : list Z) (x : Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb h x then 1 else 0) + count_occurrences t x
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => x <=? count_occurrences l x) l in
  match candidates with
  | [] => -1
  | h :: t => fold_right Z.max h t
  end.

Example test_case_new: search [4%Z; 5%Z; 6%Z; 4%Z; 3%Z; 5%Z; 5%Z] = (-1)%Z.
Proof. reflexivity. Qed.