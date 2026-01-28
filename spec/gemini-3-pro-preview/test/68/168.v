Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint enumerate (l : list Z) (idx : Z) : list (Z * Z) :=
  match l with
  | [] => []
  | x :: xs => (x, idx) :: enumerate xs (idx + 1)
  end.

Definition pluck (arr : list Z) : list Z :=
  let candidates := filter (fun p => (fst p) mod 2 =? 0) (enumerate arr 0) in
  match candidates with
  | [] => []
  | c :: cs =>
    let best := fold_left (fun acc x =>
      if (fst x) <? (fst acc) then x
      else if ((fst x) =? (fst acc)) && ((snd x) <? (snd acc)) then x
      else acc
    ) cs c in
    [fst best; snd best]
  end.

Example pluck_example : pluck [7%Z; 9%Z; 1%Z; 5%Z; 3%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 22%Z; 31%Z; 25%Z; 27%Z; 29%Z; 31%Z; 33%Z; 34%Z; 37%Z; 39%Z; 4%Z; 2%Z] = [2%Z; 22%Z].
Proof. reflexivity. Qed.