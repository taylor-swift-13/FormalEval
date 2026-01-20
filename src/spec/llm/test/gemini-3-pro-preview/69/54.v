Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occ (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb x h then 1 else 0) + count_occ x t
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => andb (0 <? x) (x <=? count_occ x l)) l in
  fold_left Z.max candidates (-1).

Example test_search: search [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 4%Z; 10%Z] = 1%Z.
Proof.
  compute. reflexivity.
Qed.