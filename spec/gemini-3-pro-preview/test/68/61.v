Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint enumerate_aux (l : list Z) (idx : Z) : list (Z * Z) :=
  match l with
  | [] => []
  | x :: xs => (x, idx) :: enumerate_aux xs (idx + 1)
  end.

Definition pluck (arr : list Z) : list Z :=
  let indexed := enumerate_aux arr 0 in
  let evens := filter (fun p => (fst p) mod 2 =? 0) indexed in
  match evens with
  | [] => []
  | h :: t =>
      let best := fold_left (fun acc x =>
        if (fst x) <? (fst acc) then x else acc
      ) t h in
      [fst best; snd best]
  end.

Example test_pluck: pluck [7; 15; 12; 21; 8; 13; 7; 15] = [8; 4].
Proof.
  compute. reflexivity.
Qed.