
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Definition count_depth_spec (s : string) (max_depth : nat) : Prop :=
  exists cnt : nat,
    (forall ch : ascii,
      (In ch (list_ascii_of_string s) -> (ch = "(" -> cnt = cnt + 1)) /\
      (In ch (list_ascii_of_string s) -> (ch = ")" -> cnt = cnt - 1))) /\
    max_depth = fold_left Nat.max (map (fun cnt => cnt) (list_ascii_of_string s)) 0.

Definition parse_nested_parens_spec (paren_string : string) (depths : list nat) : Prop :=
  depths = map (fun s => let max_depth := 0 in count_depth_spec s depths).