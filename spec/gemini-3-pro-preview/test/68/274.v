Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (l : list Z) : list Z :=
  let indexed := combine l (seq 0 (length l)) in
  let evens := filter (fun p => Z.even (fst p)) indexed in
  let is_better (p1 p2 : Z * nat) :=
    let (v1, i1) := p1 in
    let (v2, i2) := p2 in
    match Z.compare v1 v2 with
    | Lt => true
    | Eq => Nat.ltb i1 i2
    | Gt => false
    end
  in
  match evens with
  | [] => []
  | h :: t =>
    let best := fold_left (fun acc x => if is_better x acc then x else acc) t h in
    [fst best; Z.of_nat (snd best)]
  end.

Example test_case: pluck [7%Z; 9%Z; 1%Z; 5%Z; 3%Z; 4%Z; 13%Z; 17%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 9%Z; 31%Z; 33%Z; 35%Z; 36%Z; 39%Z; 4%Z; 2%Z; 21%Z] = [2%Z; 21%Z].
Proof.
  reflexivity.
Qed.