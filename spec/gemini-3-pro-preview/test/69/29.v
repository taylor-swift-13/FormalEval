Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (val : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if h =? val then 1 else 0) + count val t
  end.

Definition search (l : list Z) : Z :=
  fold_left (fun acc x => 
    if (count x l =? x) && (acc <? x) then x else acc
  ) l (-1).

Example test_case: search [1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z] = 3%Z.
Proof.
  reflexivity.
Qed.