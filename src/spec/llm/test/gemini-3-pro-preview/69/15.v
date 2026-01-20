Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count (l : list Z) (x : Z) : Z :=
  Z.of_nat (count_occ Z.eq_dec l x).

Fixpoint search_aux (n : nat) (l : list Z) : Z :=
  match n with
  | O => -1
  | S n' =>
      let z := Z.of_nat n in
      if count l z >=? z then z else search_aux n' l
  end.

Definition search (l : list Z) : Z :=
  search_aux (length l) l.

Example test_search: search [2%Z; 10%Z; 4%Z; 8%Z; 2%Z; 10%Z; 5%Z; 1%Z; 2%Z; 9%Z; 5%Z; 5%Z; 6%Z; 3%Z; 8%Z; 6%Z; 4%Z; 10%Z] = 2%Z.
Proof.
  compute.
  reflexivity.
Qed.