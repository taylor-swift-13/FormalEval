Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint count_occ (cand : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => if Z.eq_dec cand x then 1 + count_occ cand xs else count_occ cand xs
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => Z.geb (count_occ x l) x) l in
  fold_right Z.max (-1) candidates.

Example test_case_new: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 18%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 6%Z; 7%Z; 7%Z; 7%Z; 8%Z; 8%Z; 8%Z; 9%Z; 9%Z; 9%Z; 10%Z; 10%Z; 10%Z] = 2%Z.
Proof. reflexivity. Qed.