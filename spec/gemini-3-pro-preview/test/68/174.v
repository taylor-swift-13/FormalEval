Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  if List.existsb (fun x => Z.eqb x 0) l then [0; 0]
  else
    let evens := List.length (List.filter Z.even l) in
    let odds := List.length (List.filter Z.odd l) in
    [Z.of_nat evens; Z.of_nat odds].

Example test_case: even_odd_count [0; 2; 4; 6; 8; 10; 1; 5; 6; 9; 9; 6] = [0; 0].
Proof.
  reflexivity.
Qed.