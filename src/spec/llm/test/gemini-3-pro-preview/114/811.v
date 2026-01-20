Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition count_occ (l : list Z) (x : Z) : Z :=
  fold_right (fun n acc => if Z.eqb n x then acc + 1 else acc) 0 l.

Definition solution (l : list Z) : Z :=
  let valid := filter (fun x => Z.geb (count_occ l x) x) l in
  match valid with
  | [] => 0
  | x :: xs =>
    let min_val := fold_right Z.min x xs in
    let max_val := fold_right Z.max x xs in
    min_val + max_val
  end.

Example test_case: solution [-100%Z; 50%Z; -21%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; 50%Z] = -121%Z.
Proof.
  reflexivity.
Qed.