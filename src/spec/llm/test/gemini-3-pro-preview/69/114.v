Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (val : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb val h then 1 else 0) + count val t
  end.

Definition search (l : list Z) : Z :=
  let p x := Z.geb (count x l) x in
  let candidates := filter p l in
  fold_right Z.max (-1) candidates.

Example test_case : search [10%Z; 5%Z; 4%Z; 3%Z; 10%Z; 5%Z] = (-1)%Z.
Proof.
  compute. reflexivity.
Qed.