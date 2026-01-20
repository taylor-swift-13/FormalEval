
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Init.Datatypes.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Parameter is_bin_repr : Z -> string -> Prop.

Definition rounded_avg_spec (n m : Z) (result : sum Z string) : Prop :=
  if n >? m then
    result = inl (-1)
  else
    let s := n + m in
    let avg := s / 2 in
    let rem := s mod 2 in
    let rounded := 
      if rem =? 0 then avg
      else if Z.even avg then avg
      else avg + 1
    in
    exists s_bin, result = inr s_bin /\ is_bin_repr rounded s_bin.
