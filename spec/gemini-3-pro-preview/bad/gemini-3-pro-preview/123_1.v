Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition collatz_next (n : Z) : Z :=
  if Z.even n then n / 2 else 3 * n + 1.

Inductive CollatzSeq (start : Z) : Z -> Prop :=
| Collatz_Base : CollatzSeq start start
| Collatz_Step : forall x, start <> 1 -> CollatzSeq (collatz_next start) x -> CollatzSeq start x.

(* Adjusted definition to fix type error: Z.odd x returns bool, compared to true for Prop *)
Definition get_odd_collatz_spec (n : Z) (l : list Z) : Prop :=
  Sorted Z.le l /\
  (forall x, In x l <-> (CollatzSeq n x /\ Z.odd x = true)).

Example test_case : get_odd_collatz_spec 14 [1; 5; 7; 11; 13; 17].
Proof.
  unfold get_odd_collatz_spec.
  split.
  - (* Part 1: Sortedness *)
    repeat constructor; try lia.
  - (* Part 2: Equivalence *)
    intros x. split.
    + (* Direction: In list -> CollatzSeq /\ Odd *)
      intro HIn.
      simpl in HIn.
      (* Deconstruct the list membership safely *)
      repeat match goal with
      | [ H : ?y = ?z \/ ?Q |- _ ] => destruct H as [H|H]; [subst | ]
      | [ H : ?y = ?z |- _ ] => subst
      | [ H : False |- _ ] => contradiction
      end; split.
      (* Subgoal 1: Prove Oddness for each element *)
      all: try (vm_compute; reflexivity).
      (* Subgoal 2: Prove CollatzSeq 14 x for each element *)
      (* Automate the steps: try Base, otherwise Step *)
      all: repeat (first [ apply Collatz_Base | apply Collatz_Step; [ lia | simpl ] ]).
      
    + (* Direction: CollatzSeq /\ Odd -> In list *)
      intros [HSeq HOdd].
      (* Symbolic execution of the sequence starting from 14 *)
      (* We define a custom tactic to walk the sequence by inverting CollatzSeq *)
      let rec walk :=
        match goal with
        | [ H : CollatzSeq ?n x |- _ ] =>
            inversion H; subst; clear H;
            [ (* Base Case: x = n *)
              (* Check if n is odd *)
              let is_odd := eval vm_compute in (Z.odd n) in
              match is_odd with
              | true => simpl; tauto (* If odd, it must be in the list *)
              | false => 
                  (* Contradiction: HOdd says it's odd, but it's even *)
                  vm_compute in HOdd; discriminate
              end
            | (* Step Case *)
              (* If n = 1, step is impossible (1 <> 1 is false). lia solves this contradiction. *)
              try lia;
              (* Otherwise, compute next value and recurse *)
              simpl in *; walk
            ]
        end in walk.
Qed.