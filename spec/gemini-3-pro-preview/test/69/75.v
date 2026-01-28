Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (val : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb val h then 1 else 0) + count val t
  end.

Definition search (l : list Z) : Z :=
  let valid x := (x >? 0) && (count x l >=? x) in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_case: search [1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 3%Z; 2%Z; 3%Z] = 2%Z.
Proof.
  compute.
  reflexivity.
Qed.