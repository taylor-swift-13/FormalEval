Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  map (fun x => (x / 2) + (if x >? 10 then 2 else 0)) (filter Z.even l).

Example test_case : solution [7; 12; 21; 13; 8; 13; 7] = [8; 4].
Proof.
  reflexivity.
Qed.