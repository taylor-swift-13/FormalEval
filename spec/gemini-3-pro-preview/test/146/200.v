Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint below_zero_aux (l : list Z) (acc : Z) : bool :=
  match l with
  | [] => false
  | h :: t => 
      let acc' := acc + h in
      if acc' <? 0 then true else below_zero_aux t acc'
  end.

Definition below_zero (l : list Z) : Z :=
  if below_zero_aux l 0 then 0 else 1.

Example test_below_zero: below_zero [120; 121; 122; 214; 414; 8518; 21517; 2123; 918] = 1.
Proof.
  reflexivity.
Qed.