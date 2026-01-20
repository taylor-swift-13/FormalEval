Require Import ZArith.
Require Import List.
Require Import Coq.Init.Datatypes.
Require Import Lia.

Import ListNotations.
Open Scope Z_scope.

(* Specification Definitions *)

Definition is_negative (x : Z) : bool := x <? 0.
Definition is_positive (x : Z) : bool := x >? 0.

Definition largest_negative (lst : list Z) : option Z :=
  let negatives := filter (fun x => is_negative x) lst in
  match negatives with
  | nil => None
  | h :: t => Some (fold_left Z.max t h)
  end.

Definition smallest_positive (lst : list Z) : option Z :=
  let positives := filter (fun x => is_positive x) lst in
  match positives with
  | nil => None
  | h :: t => Some (fold_left Z.min t h)
  end.

Definition largest_smallest_integers_spec (lst : list Z) (result : option Z * option Z) : Prop :=
  let negatives := filter (fun x => is_negative x) lst in
  let positives := filter (fun x => is_positive x) lst in
  (fst result = match negatives with
                | nil => None
                | h :: t => Some (fold_left Z.max t h)
                end) /\
  (snd result = match positives with
                | nil => None
                | h :: t => Some (fold_left Z.min t h)
                end) /\
  (match fst result with
   | None => negatives = nil
   | Some a => In a negatives /\ a < 0 /\ (forall x, In x negatives -> x <= a)
   end) /\
  (match snd result with
   | None => positives = nil
   | Some b => In b positives /\ b > 0 /\ (forall x, In x positives -> b <= x)
   end).

(* Test Case Proof *)

Example test_largest_smallest_integers : 
  largest_smallest_integers_spec [2; 4; 1; 3; 5; 7] (None, Some 1).
Proof.
  (* Unfold the specification to expose the logic *)
  unfold largest_smallest_integers_spec.
  
  (* Simplify the filter and fold operations on the concrete list *)
  simpl.
  
  (* Split the conjunctions explicitly to handle each part *)
  split.
  - (* 1. Prove fst result is correct (None = None) *)
    reflexivity.
  - split.
    + (* 2. Prove snd result is correct (Some 1 = Some 1) *)
      reflexivity.
    + split.
      * (* 3. Prove properties for the negative part (negatives = nil) *)
        reflexivity.
      * (* 4. Prove properties for the positive part *)
        (* This is a conjunction of 3 properties *)
        split.
        -- (* 4.1 In 1 positives *)
           simpl. tauto.
        -- split.
           ++ (* 4.2 1 > 0 *)
              lia.
           ++ (* 4.3 forall x in positives, 1 <= x *)
              intros x H.
              simpl in H.
              (* Use intuition to handle the disjunctions from In and solve with lia *)
              intuition lia.
Qed.