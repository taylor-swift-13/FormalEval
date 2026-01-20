
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition char := Ascii.ascii.

Fixpoint check_balance (s : list char) (cnt : Z) : bool * Z :=
  match s with
  | nil => (true, cnt)
  | ch :: rest =>
    let new_cnt := if Ascii.eqb ch "("%char then cnt + 1 else cnt - 1 in
    if Z.ltb new_cnt 0 then (false, new_cnt)
    else check_balance rest new_cnt
  end.

Definition valid_parens (s : list char) : bool :=
  let (valid, final_cnt) := check_balance s 0 in
  valid && Z.eqb final_cnt 0.

Definition match_parens_spec (s1 s2 : list char) (result : string) : Prop :=
  (forall c, In c s1 -> c = "("%char \/ c = ")"%char) ->
  (forall c, In c s2 -> c = "("%char \/ c = ")"%char) ->
  ((valid_parens (s1 ++ s2) = true \/ valid_parens (s2 ++ s1) = true) <-> result = "Yes"%string) /\
  ((valid_parens (s1 ++ s2) = false /\ valid_parens (s2 ++ s1) = false) <-> result = "No"%string).
