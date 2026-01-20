Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint unique (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => if existsb (Z.eqb h) t then unique t else h :: unique t
  end.

Definition solution (l : list Z) : Z :=
  let negs := filter (fun x => x <? 0) l in
  match negs with
  | [] => 
      match l with
      | [] => 0
      | x :: xs => fold_right Z.min x xs
      end
  | _ => fold_right Z.add 0 (unique negs)
  end.

Example test_case: solution [-100%Z; -10%Z; -50%Z; 100%Z; 50%Z; -50%Z; -100%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; -100000%Z; -51%Z; 100%Z; 100%Z] = -100211%Z.
Proof. reflexivity. Qed.