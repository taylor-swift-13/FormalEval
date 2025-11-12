
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope Z_scope.

Fixpoint digits_list (n : Z) : list Z :=
  if n <? 10 then [n]
  else digits_list (n / 10) ++ [n mod 10].

Fixpoint prod_odd_digits (l : list Z) : option Z :=
  match l with
  | [] => None
  | d :: ds =>
    let rest := prod_odd_digits ds in
    if Z.odd d then
      match rest with
      | None => Some d
      | Some p => Some (d * p)
      end
    else rest
  end.

Definition digits_spec (n : Z) (res : Z) : Prop :=
  (n > 0) /\
  let ds := digits_list n in
  match prod_odd_digits ds with
  | None => res = 0
  | Some p => res = p
  end.
