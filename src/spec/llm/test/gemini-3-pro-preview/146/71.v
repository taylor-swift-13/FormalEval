Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition is_sorted (lst : list Z) : bool :=
  let is_asc := 
    (fix f (l : list Z) :=
       match l with
       | [] | [_] => true
       | x :: (y :: _) as t => (x <=? y) && f t
       end) lst in
  let valid_dups := 
    forallb (fun x => (length (filter (Z.eqb x) lst) <=? 2)%nat) lst in
  is_asc && valid_dups.

Definition solve (lst : list Z) : Z :=
  if is_sorted lst then 1 else 0.

Example test_case_new : solve [39; 152; 241] = 1.
Proof. reflexivity. Qed.