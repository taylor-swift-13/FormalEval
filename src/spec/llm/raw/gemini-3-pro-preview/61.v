
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope char_scope.

Fixpoint correct_bracketing_aux (s : string) (cnt : Z) : bool :=
  match s with
  | EmptyString => cnt =? 0
  | String c s' =>
      let cnt' := if c =? "(" then cnt + 1
                  else if c =? ")" then cnt - 1
                  else cnt in
      if cnt' <? 0 then false
      else correct_bracketing_aux s' cnt'
  end.

Definition correct_bracketing_spec (brackets : string) (result : bool) : Prop :=
  result = correct_bracketing_aux brackets 0.
