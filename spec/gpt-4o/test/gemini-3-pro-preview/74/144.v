Require Import List.
Require Import String.
Require Import Arith.
Import ListNotations.
Open Scope string_scope.

Definition total_match_spec (lst1 lst2 : list string) (result : list string) : Prop :=
  let c1 := fold_left (fun acc s => acc + String.length s) lst1 0 in
  let c2 := fold_left (fun acc s => acc + String.length s) lst2 0 in
  (c1 <= c2 /\ result = lst1) \/ (c1 > c2 /\ result = lst2).

Example test_total_match_1: total_match_spec 
  ["98765432170"; "AbCdEfG"; "HijKlMnOp"; "QrStUvWxyZ"; "AaBbCcDdEeFfGgHhIiJjKkLlMmNnOoPpQqRrSsT"; "UuVvWwXxYyZz"; "HijKlMnOp"] 
  ["abcdefg"; "hijknlmnop"; "qrstuv"; "wxyz"] 
  ["abcdefg"; "hijknlmnop"; "qrstuv"; "wxyz"].
Proof.
  unfold total_match_spec.
  right.
  split.
  - vm_compute. repeat constructor.
  - reflexivity.
Qed.