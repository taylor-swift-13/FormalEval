Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (val : Z) (l : list Z) : nat :=
  match l with
  | [] => 0%nat
  | h :: t => if Z.eq_dec h val then S (count val t) else count val t
  end.

Definition search (l : list Z) : Z :=
  let predicate x := (0 <? x) && (x <=? Z.of_nat (count x l)) in
  let valid := filter predicate l in
  fold_right Z.max (-1) valid.

Example test_search : search [5%Z; 5%Z; 5%Z; 5%Z; 5%Z; 4%Z; 5%Z; 5%Z; 5%Z] = 5%Z.
Proof.
  reflexivity.
Qed.