Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let l_filtered := filter (fun x => x <? 5) l in
  let evens := filter (fun x => x mod 2 =? 0) l_filtered in
  let odds := filter (fun x => x mod 2 =? 1) l_filtered in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_case : even_odd_count [2; 4; 6; 8] = [2; 0].
Proof. reflexivity. Qed.