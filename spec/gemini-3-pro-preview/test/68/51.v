Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  flat_map (fun x => 
    if Z.even x then 
      if x >? 4 then [x; x / 2] else [x / 2]
    else []) l.

Example test_case: solution [7%Z; 15%Z; 21%Z; 13%Z; 8%Z; 13%Z; 7%Z] = [8%Z; 4%Z].
Proof. reflexivity. Qed.