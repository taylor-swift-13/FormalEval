Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.

Import ListNotations.

Definition row (p : nat * nat) : nat := fst p.
Definition col (p : nat * nat) : nat := snd p.

Definition pair_order (p1 p2 : nat * nat) : Prop :=
  row p1 < row p2 \/ (row p1 = row p2 /\ col p1 > col p2).

Definition match_pos (lst : list (list Z)) (x : Z) (i j : nat) : Prop :=
  match nth_error lst i with
  | Some r =>
      match nth_error r j with
      | Some v => v = x
      | None => False
      end
  | None => False
  end.

Definition get_row_spec (lst : list (list Z)) (x : Z) (res : list (nat * nat)) : Prop :=
  NoDup res /\
  StronglySorted pair_order res /\
  forall i j, In (i, j) res <-> match_pos lst x i j.

(* Use Z_scope for integer literals in lists, but we must be careful with nat literals *)
Open Scope Z_scope.

Example test_case : 
  get_row_spec 
    [[1; 2; 3; 4; 5; 6]; [1; 2; 3; 4; 1; 6]; [1; 2; 3; 4; 5; 1]] 
    1 
    [(0%nat, 0%nat); (1%nat, 4%nat); (1%nat, 0%nat); (2%nat, 5%nat); (2%nat, 0%nat)].
Proof.
  unfold get_row_spec.
  split.
  - (* NoDup *)
    repeat constructor; intro H; simpl in H; repeat destruct H as [H|H]; inversion H.
  - split.
    + (* StronglySorted *)
      unfold pair_order, row, col.
      repeat constructor.
      all: simpl; try lia.
    + (* Equivalence *)
      intros i j. split.
      * (* In -> match_pos *)
        intro H.
        simpl in H.
        (* Verify each element in the result list matches the input at that position *)
        repeat destruct H as [H | H]; inversion H; subst; simpl; reflexivity.
      * (* match_pos -> In *)
        intro H.
        unfold match_pos in H.
        (* Destruct i to handle each row *)
        destruct i.
        { (* i = 0 *)
          do 6 (destruct j; [| simpl in H ]).
          - left; reflexivity. (* j=0 *)
          - discriminate.
          - discriminate.
          - discriminate.
          - discriminate.
          - discriminate.
          - contradiction.
        }
        destruct i.
        { (* i = 1 *)
          do 6 (destruct j; [| simpl in H ]).
          - right; right; left; reflexivity. (* j=0, matches (1,0) *)
          - discriminate.
          - discriminate.
          - discriminate.
          - right; left; reflexivity. (* j=4, matches (1,4) *)
          - discriminate.
          - contradiction.
        }
        destruct i.
        { (* i = 2 *)
          do 6 (destruct j; [| simpl in H ]).
          - right; right; right; right; left; reflexivity. (* j=0, matches (2,0) *)
          - discriminate.
          - discriminate.
          - discriminate.
          - discriminate.
          - right; right; right; left; reflexivity. (* j=5, matches (2,5) *)
          - contradiction.
        }
        { (* i > 2 *)
          simpl in H. contradiction.
        }
Qed.