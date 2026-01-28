Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint even_odd_count_aux (l : list Z) (e o : Z) : list Z :=
  match l with
  | [] => [e; o]
  | x :: xs => if x =? 1 then [e; o]
               else if Z.even x then even_odd_count_aux xs (e + 1) o
               else even_odd_count_aux xs e (o + 1)
  end.

Definition even_odd_count (l : list Z) : list Z :=
  even_odd_count_aux l 0 0.

Example test_case: even_odd_count [2; 4; 1; 6; 8; 10; 8; 1] = [2; 0].
Proof.
  reflexivity.
Qed.