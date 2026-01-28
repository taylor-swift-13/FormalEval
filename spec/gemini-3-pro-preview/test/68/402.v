Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition pluck (l : list Z) : list Z :=
  let indices := map Z.of_nat (seq 0 (length l)) in
  let indexed := combine l indices in
  let candidates := filter (fun p => (fst p) mod 2 =? 0) indexed in
  match candidates with
  | [] => []
  | h :: t =>
      let best := fold_left (fun acc x => if (fst x) <? (fst acc) then x else acc) t h in
      [fst best; snd best]
  end.

Example test_pluck : pluck [0%Z; 1%Z; 5%Z; 25%Z; 7%Z; 1%Z; 1%Z] = [0%Z; 0%Z].
Proof. reflexivity. Qed.