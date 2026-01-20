Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint below_zero_aux (l : list Z) (acc : Z) : Z :=
  match l with
  | [] => 1
  | h :: t =>
      let acc' := acc + h in
      if acc' <? 0 then 0 else below_zero_aux t acc'
  end.

Definition below_zero (l : list Z) : Z :=
  below_zero_aux l 0.

Example test_below_zero : below_zero [39%Z; 152%Z; 241%Z; -339%Z] = 1%Z.
Proof. reflexivity. Qed.