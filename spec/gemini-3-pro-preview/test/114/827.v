Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let step (acc : Z * Z) (y : Z) :=
        let (min_s, cur_s) := acc in
        let cur_s' := cur_s + y in
        let min_s' := Z.min min_s cur_s' in
        let cur_s'' := if cur_s' >? 0 then 0 else cur_s' in
        (min_s', cur_s'')
      in
      let (res, _) := fold_left step xs (x, if x >? 0 then 0 else x) in
      res
  end.

Example test_minSubArraySum:
  minSubArraySum [1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -6%Z; 2%Z; -1%Z; -1%Z] = -6%Z.
Proof.
  compute. reflexivity.
Qed.