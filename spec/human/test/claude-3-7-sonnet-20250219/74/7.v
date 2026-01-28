Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.
Open Scope string_scope.

Definition problem_74_pre (lst1 lst2 : list string) : Prop := True.

Definition problem_74_spec (lst1 lst2 output : list string) : Prop :=
  let sum := fun l => fold_left (fun acc s => acc + String.length s) l 0 in
  (sum lst1 <= sum lst2 /\ output = lst1) \/
  (sum lst1 > sum lst2 /\ output = lst2).

Example test_total_match_hi_admin:
  problem_74_spec ["hi"; "admin"] ["hI"; "hi"; "hii"] ["hi"; "admin"].
Proof.
  unfold problem_74_spec.
  simpl.
  left.
  split.
  - simpl. (* sum ["hi"; "admin"] = 2 + 5 = 7 *)
    simpl. (* sum ["hI"; "hi"; "hii"] = 2 + 2 + 3 = 7 *)
    apply Nat.le_refl.
  - reflexivity.
Qed.