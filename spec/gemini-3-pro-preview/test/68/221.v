Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (l : list Z) : list Z :=
  let indexed := combine l (seq 0 (length l)) in
  let evens := filter (fun p => (fst p) mod 2 =? 0) indexed in
  let fix find_min (l : list (Z * nat)) (acc : option (Z * nat)) : option (Z * nat) :=
    match l with
    | [] => acc
    | (v, i) :: t =>
      match acc with
      | None => find_min t (Some (v, i))
      | Some (min_v, min_i) =>
        if v <? min_v then find_min t (Some (v, i))
        else find_min t acc
      end
    end in
  match find_min evens None with
  | Some (v, i) => [v; Z.of_nat i]
  | None => []
  end.

Example pluck_test : pluck [7%Z; 9%Z; 1%Z; 5%Z; 3%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 22%Z; 31%Z; 25%Z; 27%Z; 29%Z; 31%Z; 33%Z; 34%Z; 37%Z; 39%Z; 4%Z; 2%Z; 29%Z] = [2%Z; 22%Z].
Proof.
  compute. reflexivity.
Qed.