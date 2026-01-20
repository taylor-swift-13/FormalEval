Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition triples_sum_to_zero_spec (l : list Z) (res : bool) : Prop :=
  res = true <->
  (exists i j k : nat,
    (i < length l)%nat /\ (j < length l)%nat /\ (k < length l)%nat /\
    i <> j /\ i <> k /\ j <> k /\
    nth i l 0 + nth j l 0 + nth k l 0 = 0).

Example test_triples_sum_to_zero : triples_sum_to_zero_spec [1; 3; 5; -1] false.
Proof.
  unfold triples_sum_to_zero_spec.
  split.
  - (* Direction: false = true -> ... (contradiction) *)
    intros H. discriminate H.
  - (* Direction: exists ... -> false = true (contradiction) *)
    intros H.
    destruct H as [i [j [k [Hi [Hj [Hk [Hij [Hik [Hjk Hsum]]]]]]]]].
    (* Simplify length hypotheses to concrete bounds *)
    simpl in Hi, Hj, Hk.

    (* Case analysis on index i: 0, 1, 2, 3, or >= 4 *)
    destruct i as [|i]; [| destruct i as [|i]; [| destruct i as [|i]; [| destruct i as [|i]; [| simpl in Hi; lia ]]]].
    
    (* Case analysis on index j for all resulting subgoals *)
    all: destruct j as [|j]; [| destruct j as [|j]; [| destruct j as [|j]; [| destruct j as [|j]; [| simpl in Hj; lia ]]]].
    
    (* Case analysis on index k for all resulting subgoals *)
    all: destruct k as [|k]; [| destruct k as [|k]; [| destruct k as [|k]; [| destruct k as [|k]; [| simpl in Hk; lia ]]]].

    (* Now we have concrete indices for all valid combinations.
       1. Simplify the sum expression (lookup in the list).
       2. Use congruence to handle cases where indices are not distinct (contradicting Hij, Hik, Hjk).
       3. Use lia to handle cases where the sum is not zero. *)
    all: simpl in Hsum; try congruence; try lia.
Qed.