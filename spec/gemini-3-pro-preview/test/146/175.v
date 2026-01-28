Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
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

Example test_case: below_zero [120; 122; 414; 214; 357; 8518; 21517; 918; 2123; 21517] = 1.
Proof.
  reflexivity.
Qed.