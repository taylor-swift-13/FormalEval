Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_40_pre (input : list Z) : Prop := True.

Definition problem_40_spec (input : list Z) (output : bool) : Prop :=
  (exists i j k : nat,
    (i <> j) /\ (i <> k) /\ (j <> k) /\
    (i < length input)%nat /\
    (j < length input)%nat /\
    (k < length input)%nat /\
    (nth i input 0 + nth j input 0 + nth k input 0 = 0))
  <-> (output = true).

Example test_case : problem_40_spec [-1; -2; 1] false.
Proof.
  unfold problem_40_spec.
  split.
  - (* (Exists ...) -> false = true *)
    intros (i & j & k & Hij & Hik & Hjk & Hi & Hj & Hk & Hsum).
    (* Simplify the bounds to concrete numbers *)
    simpl in Hi, Hj, Hk.
    
    (* Exhaustively decompose indices i, j, k based on the bounds < 3.
       We use repeat destruct to break down the natural numbers.
       'try lia' eliminates cases where the index exceeds the bound. *)
    repeat (destruct i as [|i]; [| try lia]).
    all: repeat (destruct j as [|j]; [| try lia]).
    all: repeat (destruct k as [|k]; [| try lia]).

    (* Now i, j, k are concrete values (0, 1, 2) in all subgoals.
       We simplify the nth function and check for contradictions in 
       distinctness (Hij, etc.) or the sum (Hsum). *)
    all: simpl in Hsum; try lia.
    
  - (* false = true -> ... *)
    discriminate.
Qed.