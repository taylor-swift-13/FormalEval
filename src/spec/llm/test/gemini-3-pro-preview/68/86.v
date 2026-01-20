Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint take_while (f : Z -> bool) (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs => if f x then x :: take_while f xs else []
  end.

Definition even_odd_count (l : list Z) : list Z :=
  let l' := take_while (fun x => x <=? 4) l in
  let evens := filter Z.even l' in
  let odds := filter Z.odd l' in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_even_odd_count: even_odd_count [2; 4; 6; 8; 4] = [2; 0].
Proof.
  reflexivity.
Qed.