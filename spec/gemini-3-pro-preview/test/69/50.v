Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : nat :=
  match l with
  | [] => 0%nat
  | h :: t => if Z.eq_dec h x then S (count x t) else count x t
  end.

Fixpoint search_aux (n : nat) (l : list Z) : Z :=
  match n with
  | 0%nat => -1
  | S k =>
      let z := Z.of_nat (S k) in
      if (Z.of_nat (count z l) >=? z) then z
      else search_aux k l
  end.

Definition search (l : list Z) : Z :=
  search_aux (length l) l.

Example test_case_1 : search [1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 2%Z] = 2%Z.
Proof. reflexivity. Qed.