Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occurrences (l : list Z) (x : Z) : Z :=
  match l with
  | [] => 0
  | h :: t => if Z.eq_dec h x then 1 + count_occurrences t x else count_occurrences t x
  end.

Definition search (lst : list Z) : Z :=
  let candidates := filter (fun x => count_occurrences lst x >=? x) lst in
  fold_right Z.max (-1) candidates.

Example test_case: search [20%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z] = 3%Z.
Proof.
  compute. reflexivity.
Qed.