Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let fix aux (l : list Z) (e o : Z) : list Z :=
    match l with
    | [] => [e; o]
    | x :: xs =>
      if x >? 4 then [e; o]
      else if Z.even x then aux xs (e + 1) o
      else aux xs e (o + 1)
    end
  in aux l 0 0.

Example test_even_odd_count: even_odd_count [2; 4; 7; 4] = [2; 0].
Proof. reflexivity. Qed.