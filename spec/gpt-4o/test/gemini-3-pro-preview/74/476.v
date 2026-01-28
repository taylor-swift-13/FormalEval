Require Import List.
Require Import String.
Require Import Arith.
Import ListNotations.

Definition total_match_spec (lst1 lst2 : list string) (result : list string) : Prop :=
  let c1 := fold_left (fun acc s => acc + String.length s) lst1 0 in
  let c2 := fold_left (fun acc s => acc + String.length s) lst2 0 in
  (c1 <= c2 /\ result = lst1) \/ (c1 > c2 /\ result = lst2).

Example test_total_match_complex: total_match_spec 
  ["AbCdEf"; "HijKlMnOp"; "QrStUvWxyZ"; "AaBbCcDdEeFfGgHhIiJjKkLlMmNnOoPpQqRrSsT"; "The"; "UuVvWwXxYyZz"; "QrStUvWxyZ"; "QrStUvWxyZ"; "UuVvWwXxYyZz"]%string
  ["AbCdEf"; "HijKlMnOp"; "QrStUvWxyZ"; "AaBbCcDdEeFfGgHhIiJjKkLlMmNnOoPpQqRrSsT"; "The"; "UuVvWwXxYyZz"; "QrStUvWxyZ"; "QrStUvWxyZ"; "UuVvWwXxYyZz"]%string
  ["AbCdEf"; "HijKlMnOp"; "QrStUvWxyZ"; "AaBbCcDdEeFfGgHhIiJjKkLlMmNnOoPpQqRrSsT"; "The"; "UuVvWwXxYyZz"; "QrStUvWxyZ"; "QrStUvWxyZ"; "UuVvWwXxYyZz"]%string.
Proof.
  unfold total_match_spec.
  left.
  split.
  - apply le_n.
  - reflexivity.
Qed.