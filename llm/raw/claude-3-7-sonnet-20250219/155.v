
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition even_odd_count_spec (num : Z) (even_count odd_count : nat) : Prop :=
  let digits := 
    fix digits_of_string (s : string) : list ascii :=
      match s with
      | EmptyString => []
      | String c rest => c :: digits_of_string rest
      end
  in
  let s := (Z.to_string num) in
  let ds := digits s in
  even_count = length (filter (fun c => if (c =? "0")%char || (c =? "2")%char || (c =? "4")%char || (c =? "6")%char || (c =? "8")%char then true else false) ds)
  /\
  odd_count = length (filter (fun c => if (c =? "1")%char || (c =? "3")%char || (c =? "5")%char || (c =? "7")%char || (c =? "9")%char then true else false) ds).
