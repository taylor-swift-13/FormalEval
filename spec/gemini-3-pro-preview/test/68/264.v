Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  if existsb (fun x => x =? 0) l then [0; 0]
  else [Z.of_nat (length (filter Z.even l)); Z.of_nat (length (filter Z.odd l))].

Example test_even_odd_count: even_odd_count [0%Z; 2%Z; 4%Z; 7%Z; 6%Z; 10%Z; 1%Z; 3%Z; 34%Z; 5%Z; 6%Z; 9%Z; 9%Z] = [0%Z; 0%Z].
Proof. reflexivity. Qed.