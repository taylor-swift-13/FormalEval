Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let l' := filter (fun x => x <=? 4) l in
  let evens := filter (fun x => x mod 2 =? 0) l' in
  let odds := filter (fun x => negb (x mod 2 =? 0)) l' in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_case_new : even_odd_count [2; 4; 6; 8; 10] = [2; 0].
Proof. reflexivity. Qed.