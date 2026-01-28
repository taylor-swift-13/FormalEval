Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  let (e, o) := fold_left (fun (acc : Z * Z) (x : Z) =>
    let (ec, oc) := acc in
    if Z.even x then (ec + 1, oc) else (ec, oc + 1)
  ) l (0, 0) in
  [e; o].

Example test_case_new : solution [10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 21; 10000; 27; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 39; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 0; 1; 10000; 10000] = [35; 35].
Proof. reflexivity. Qed.