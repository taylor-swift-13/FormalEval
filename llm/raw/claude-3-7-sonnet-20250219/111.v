
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Structures.Equalities.
Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.MSets.MSetList.
Require Import Coq.Bool.Bool.
Import ListNotations.

Module String_as_OT := 
  struct
    Definition t := string.
    Definition eq := @eq string.
    Definition lt := String.lt.
    Definition eq_refl := @eq_refl string.
    Definition eq_sym := @eq_sym string.
    Definition eq_trans := @eq_trans string.
    Definition lt_trans := String.lt_trans.
    Definition lt_not_eq := String.lt_not_eq.
    Definition compare := String.compare.
    Definition compare_spec := String.compare_spec.
  End.

Module M := FMapList.Make(String_as_OT).
Module MFacts := WFacts_fun String_as_OT M.

Definition histogram_spec (test : string) (ans : M.t nat) : Prop :=
  let words := filter (fun w => negb (String.eqb w "")) (String.split " " test) in
  let counts := 
    fold_left (fun acc w => 
      match M.find w acc with
      | Some n => M.add w (S n) acc
      | None => M.add w 1 acc
      end) words (M.empty nat) in
  let max_count := 
    match fold_left (fun acc w => 
      match M.find w counts with
      | Some n => if Nat.ltb acc n then n else acc
      | None => acc
      end) (M.fold (fun _ n acc => n :: acc) counts []) 0 with
    | 0 => 0
    | m => m
    end in
  (forall k n, M.find k ans = Some n <-> M.find k counts = Some n /\ n = max_count) /\
  (max_count = 0 -> M.Empty ans).
