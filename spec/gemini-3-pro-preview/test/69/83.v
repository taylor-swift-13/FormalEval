Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | y :: tl => if Z.eq_dec y x then 1 + count x tl else count x tl
  end.

Definition search (l : list Z) : Z :=
  let check x := count x l >=? x in
  let valid := filter check l in
  fold_right Z.max (-1) valid.

Example test_case_1: search [1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 4%Z; 7%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 3%Z; 4%Z] = 4%Z.
Proof.
  compute.
  reflexivity.
Qed.