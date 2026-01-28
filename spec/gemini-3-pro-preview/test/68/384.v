Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  match l with
  | [] => [0; 0]
  | h :: t =>
    let n := Z.to_nat h in
    let taken := firstn n l in
    let evens := length (filter Z.even taken) in
    let odds := length (filter (fun x => negb (Z.even x)) taken) in
    [Z.of_nat evens; Z.of_nat odds]
  end.

Example test_case: even_odd_count [2; 4; 6; 8; 10; 1; 4; 5; 7; 9] = [2; 0].
Proof.
  compute. reflexivity.
Qed.