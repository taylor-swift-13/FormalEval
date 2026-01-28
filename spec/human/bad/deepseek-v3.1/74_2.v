Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.

Import ListNotations.

Definition problem_74_spec (lst1 lst2 output : list string) : Prop :=
  let sum := fun l => fold_left (fun acc s => acc + String.length s) l 0 in
  (sum lst1 <= sum lst2 /\ output = lst1) \/
  (sum lst1 > sum lst2 /\ output = lst2).

Example test_new_case : 
  problem_74_spec [["hi"; "admin"]; ["hi"; "hi"]] ["hi"; "hi"] [].
Proof.
  unfold problem_74_spec.
  simpl.
  (* Calculate sums *)
  set (sum1 := fold_left (fun acc s => acc + String.length s) [["hi"; "admin"]; ["hi"; "hi"]] 0).
  set (sum2 := fold_left (fun acc s => acc + String.length s) ["hi"; "hi"] 0).
  
  (* Compute individual string lengths *)
  (* "hi" = 2, "admin" = 5 *)
  (* First list sum: "hi"=2, "admin"=5, total=7; second list: "hi"=2, "hi"=2, total=4 *)
  (* So sum1=7, sum2=4, sum1 > sum2, hence output should be lst2 *)
  
  assert (sum1 = 7).
  {
    simpl.
    reflexivity.
  }
  assert (sum2 = 4).
  {
    simpl.
    reflexivity.
  }
  right.
  split.
  - lia.
  - reflexivity.
Qed.