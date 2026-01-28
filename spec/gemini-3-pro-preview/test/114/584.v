Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count (l : list Z) (x : Z) : Z :=
  fold_right (fun y c => if Z.eq_dec y x then c + 1 else c) 0 l.

Definition search (l : list Z) : Z :=
  let valid := filter (fun x => x <=? count l x) l in
  match valid with
  | [] => -1
  | h :: t => fold_right Z.min h t
  end.

Example test_search:
  search [-1; 1; -1; 1; -1; 1; -1; 0; 1; -1; 1; -1; 1; -1; 1; -1; 30; -1; 1; -1; 50; -1; 1; -1; 1; -1; 1; 2; -1; 1; 1] = -1.
Proof.
  reflexivity.
Qed.