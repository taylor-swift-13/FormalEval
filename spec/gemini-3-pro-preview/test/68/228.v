Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint take_while {A} (p : A -> bool) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => if p x then x :: take_while p xs else []
  end.

Definition solution (l : list Z) : list Z :=
  let l' := take_while (fun x => x <? 6) l in
  let evens := filter Z.even l' in
  let odds := filter Z.odd l' in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_case_2 : solution [2; 2; 6; 8; 10; 2] = [2; 0].
Proof. reflexivity. Qed.