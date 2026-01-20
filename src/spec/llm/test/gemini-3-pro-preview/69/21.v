Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occ (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | y :: tl => (if Z.eq_dec y x then 1 else 0) + count_occ x tl
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => x <=? count_occ x l) l in
  fold_right Z.max (-1) candidates.

Example test_case: search [10%Z] = -1%Z.
Proof. reflexivity. Qed.