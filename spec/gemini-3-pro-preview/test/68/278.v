Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition solution (l : list Z) : list Z :=
  map (fun x => Z.div x 2) (filter Z.even l).

Example check : solution [1%Z; 37%Z; 7%Z; 9%Z; 1%Z] = [].
Proof.
  simpl.
  reflexivity.
Qed.