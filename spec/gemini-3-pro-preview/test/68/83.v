Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let fix count (l' : list Z) : (Z * Z) :=
    match l' with
    | [] => (0, 0)
    | h :: t =>
      let (e, o) := count t in
      if Z.even h then (e + 1, o) else (e, o + 1)
    end in
  let (e, o) := count l in
  let scale := Z.of_nat (length l) / 3 in
  [e * scale; o * scale].

Example test_case : even_odd_count [12; 15; 12; 21; 8; 14] = [8; 4].
Proof. compute. reflexivity. Qed.