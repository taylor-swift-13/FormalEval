Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solve (l : list Z) : list Z :=
  map (fun x => x / 2) (filter Z.even l).

Example test_case_1 : solve [1; 303; 5; 9] = [].
Proof.
  compute. reflexivity.
Qed.