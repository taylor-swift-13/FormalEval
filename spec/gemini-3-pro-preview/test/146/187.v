Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition add_elements (arr : list Z) (k : Z) : Z :=
  let l := firstn (Z.to_nat k) arr in
  let is_valid (n : Z) : bool := (n >? -10) && (n <? 100) in
  fold_right (fun x acc => if is_valid x then x + acc else acc) 0 l.

Example test_case : add_elements [120; 414; 214; 8518; 21517; 2123; 918] 7 = 0.
Proof.
  compute. reflexivity.
Qed.