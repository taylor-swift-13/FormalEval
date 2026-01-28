Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occ (lst : list Z) (x : Z) : Z :=
  match lst with
  | [] => 0
  | h :: t => (if x =? h then 1 else 0) + count_occ t x
  end.

Definition search (lst : list Z) : Z :=
  let p x := (x >? 0) && (count_occ lst x >=? x) in
  fold_right Z.max (-1) (filter p lst).

Example test_case : search [10%Z; 5%Z; 5%Z; 4%Z; 3%Z; 5%Z; 8%Z] = (-1)%Z.
Proof.
  reflexivity.
Qed.