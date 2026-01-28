Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope string_scope.

Definition problem_74_pre (lst1 lst2 : list string) : Prop := True.

Definition problem_74_spec (lst1 lst2 output : list string) : Prop :=
  let sum := fun l => fold_left (fun acc s => acc + String.length s) l 0 in
  (sum lst1 <= sum lst2 /\ output = lst1) \/
  (sum lst1 > sum lst2 /\ output = lst2).

Example test_case_2 : problem_74_spec 
  ["YyouOU"; "ARHijKlMnOpE"; "HELLO"; "WORLD"; "HOW"; "AAppleRE"]
  ["YyouOU"; "ARHijKlMnOpE"; "HELLO"; "WORLD"; "HOW"; "AAppleRE"]
  ["YyouOU"; "ARHijKlMnOpE"; "HELLO"; "WORLD"; "HOW"; "AAppleRE"].
Proof.
  unfold problem_74_spec.
  left.
  split.
  - simpl. lia.
  - reflexivity.
Qed.