Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Import List.
Open Scope Z_scope.

Definition solve (l : list Z) : list Z :=
  let indexed := combine l (seq 0 (length l)) in
  let evens := filter (fun p => (fst p) mod 2 =? 0) indexed in
  match evens with
  | [] => []
  | h :: t =>
    let best := fold_left (fun acc p => if fst p <? fst acc then p else acc) t h in
    [fst best; Z.of_nat (snd best)]
  end.

Example test_case: solve [5%Z; 10%Z; 15%Z; 9%Z; 20%Z; 15%Z; 10%Z] = [10%Z; 1%Z].
Proof.
  compute. reflexivity.
Qed.