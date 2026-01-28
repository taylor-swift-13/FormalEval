Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  List.map (fun x => Z.div x 2) (List.filter Z.even l).

Example test_case: solution [1%Z; 3%Z; 5%Z; 31%Z; 7%Z; 9%Z] = [].
Proof.
  simpl.
  reflexivity.
Qed.