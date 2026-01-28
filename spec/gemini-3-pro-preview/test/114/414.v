Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (l : list Z) (x : Z) : Z :=
  fold_right (fun y acc => if Z.eqb x y then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => Z.eqb (count_occurrences l x) x) l in
  match candidates with
  | [] => -1
  | h :: t => fold_right Z.min h t
  end.

Example search_example : search [1; -1; 1; -1; 1; 9; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 30; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; 1] = -1.
Proof.
  reflexivity.
Qed.