Require Import List.
Require Import String.
Require Import Arith.
Import ListNotations.

Definition total_match_spec (lst1 lst2 : list string) (result : list string) : Prop :=
  let c1 := fold_left (fun acc s => acc + String.length s) lst1 0 in
  let c2 := fold_left (fun acc s => acc + String.length s) lst2 0 in
  (c1 <= c2 /\ result = lst1) \/ (c1 > c2 /\ result = lst2).

Example test_total_match: total_match_spec 
  ["abcdefg"; "hijknlmnop"; "qrstuv"; "wxyz"]%string
  ["AbCdEfG"; "HijKlMnOp"; "QrStUvWxyZ"; "AaBbCcDdEeFfGgHhIiJjKkLlMmNnOoPpQqRrSsT"; "UuVvWwXxYyZz"]%string
  ["abcdefg"; "hijknlmnop"; "qrstuv"; "wxyz"]%string.
Proof.
  unfold total_match_spec.
  simpl.
  left.
  split.
  - repeat constructor.
  - reflexivity.
Qed.