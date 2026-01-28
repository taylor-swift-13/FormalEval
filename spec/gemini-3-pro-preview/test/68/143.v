Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_even (n : Z) : bool := (n mod 2 =? 0).

Definition even_odd_count (l : list Z) : list Z :=
  match l with
  | [] => [0; 0]
  | x :: _ =>
    let n := Z.to_nat x in
    let prefix := firstn n l in
    let evens := filter is_even prefix in
    let odds := filter (fun x => negb (is_even x)) prefix in
    [Z.of_nat (length evens); Z.of_nat (length odds)]
  end.

Example test_even_odd_count: even_odd_count [2; 4; 6; 8; 2; 3; 2] = [2; 0].
Proof.
  reflexivity.
Qed.