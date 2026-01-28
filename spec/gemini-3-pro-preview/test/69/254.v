Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (l : list Z) (x : Z) : Z :=
  match l with
  | [] => 0
  | h :: t => if h =? x then 1 + count t x else count t x
  end.

Definition search (l : list Z) : Z :=
  let p x := (x >? 0) && (count l x >=? x) in
  let candidates := filter p l in
  fold_right Z.max (-1) candidates.

Example test_search: search [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 6%Z; 7%Z; 8%Z; 10%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z] = 1%Z.
Proof.
  compute.
  reflexivity.
Qed.