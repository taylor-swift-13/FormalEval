Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  match l with
  | [] => [0; 0]
  | h :: t =>
    let n := Z.to_nat h in
    let sub := firstn n l in
    let evens := length (filter (fun x => Z.even x) sub) in
    let odds := length (filter (fun x => negb (Z.even x)) sub) in
    [Z.of_nat evens; Z.of_nat odds]
  end.

Example test_case_2: solution [2; 6; 8; 10] = [2; 0].
Proof. reflexivity. Qed.