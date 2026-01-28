Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := length (filter (fun x => x mod 2 =? 0) l) in
  let odds := length (filter (fun x => negb (x mod 2 =? 0)) l) in
  [Z.of_nat evens; Z.of_nat odds].

Example test_case_new : even_odd_count [5%Z; 3%Z; 1%Z; 5%Z; 7%Z; 2%Z; 0%Z; 1%Z] = [2%Z; 6%Z].
Proof. reflexivity. Qed.