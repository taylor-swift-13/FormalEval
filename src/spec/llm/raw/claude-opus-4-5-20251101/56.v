 
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope Z_scope.

Fixpoint check_brackets (brackets : list ascii) (cnt : Z) : bool :=
  match brackets with
  | nil => Z.eqb cnt 0
  | x :: xs =>
    let cnt' := if Ascii.eqb x "<"%char then cnt + 1
                else if Ascii.eqb x ">"%char then cnt - 1
                else cnt in
    if Z.ltb cnt' 0 then false
    else check_brackets xs cnt'
  end.

Definition correct_bracketing_spec (brackets : list ascii) (result : bool) : Prop :=
  result = check_brackets brackets 0.
