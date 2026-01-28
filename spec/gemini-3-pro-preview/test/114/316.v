Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let step (acc : Z * Z) (n : Z) :=
      let (curr, min_s) := acc in
      let curr' := curr + n in
      let min_s' := Z.min min_s curr' in
      let curr'' := if curr' >? 0 then 0 else curr' in
      (curr'', min_s')
    in
    let init_curr := if x >? 0 then 0 else x in
    let init_min := x in
    let (_, res) := fold_left step xs (init_curr, init_min) in
    res
  end.

Example test_minSubArraySum: minSubArraySum [1%Z; -1%Z; 1%Z; -1%Z; 0%Z; 1%Z; -1%Z; 1%Z; -1%Z; -6%Z; 1%Z; 40%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 30%Z; -1%Z; -51%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z] = -53%Z.
Proof. reflexivity. Qed.