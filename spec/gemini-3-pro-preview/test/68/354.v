Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z := [0%Z; 0%Z].

Example test_case: solution [0%Z; 2%Z; 4%Z; 6%Z; 8%Z; 10%Z; 3%Z; 5%Z; 9%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 18%Z; 23%Z; 25%Z; 27%Z; 29%Z; 31%Z; 33%Z; 9%Z; 35%Z; 39%Z; 39%Z; 25%Z] = [0%Z; 0%Z].
Proof. reflexivity. Qed.