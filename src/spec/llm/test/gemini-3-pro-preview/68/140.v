Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_even (n : Z) : bool := Z.even n.

Fixpoint take (n : nat) (l : list Z) : list Z :=
  match n with
  | O => []
  | S n' => match l with
            | [] => []
            | x :: xs => x :: take n' xs
            end
  end.

Fixpoint count_aux (l : list Z) : Z * Z :=
  match l with
  | [] => (0, 0)
  | x :: xs =>
      let (e, o) := count_aux xs in
      if is_even x then (e + 1, o) else (e, o + 1)
  end.

Definition even_odd_count (l : list Z) : list Z :=
  match l with
  | [] => [0; 0]
  | x :: xs =>
      let n := Z.to_nat x in
      let l' := take n l in
      let (e, o) := count_aux l' in
      [e; o]
  end.

Example test_case: even_odd_count [2; 2; 4; 6; 8; 10; 2] = [2; 0].
Proof. reflexivity. Qed.