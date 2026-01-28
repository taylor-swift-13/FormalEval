Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count (l : list Z) (x : Z) : Z :=
  fold_right (fun n acc => if Z.eqb n x then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let counts := map (fun x => (x, count l x)) l in
  let valid := filter (fun p => Z.eqb (fst p) (snd p)) counts in
  let valid_vals := map fst valid in
  fold_right Z.max (-1) valid_vals.

Example test_search : search [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 10%Z; 5%Z; 7%Z; 8%Z; 9%Z; 10%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 5%Z; 6%Z; 18%Z; 7%Z; 8%Z; 9%Z; 10%Z; 8%Z] = 5%Z.
Proof.
  reflexivity.
Qed.