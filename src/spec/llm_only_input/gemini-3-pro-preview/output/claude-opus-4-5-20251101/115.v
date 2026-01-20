Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.micromega.Lia.

Import ListNotations.

Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition ceil_div (a b : Z) : Z :=
  (a + b - 1) / b.

Definition max_fill_spec (grid : list (list Z)) (capacity : Z) (result : Z) : Prop :=
  capacity > 0 /\
  (forall row, In row grid -> forall x, In x row -> x = 0 \/ x = 1) /\
  result = fold_right (fun row acc => acc + ceil_div (sum_list row) capacity) 0 grid.

Example test_max_fill :
  max_fill_spec [[0; 0; 1; 0]; [0; 1; 0; 0]; [1; 1; 1; 1]] 1 6.
Proof.
  unfold max_fill_spec.
  split.
  - (* Goal 1: capacity > 0 *)
    lia.
  - split.
    + (* Goal 2: Elements are 0 or 1 *)
      intros row Hrow x Hx.
      simpl in Hrow.
      (* Decompose the grid rows *)
      repeat match goal with
      | [ H : _ \/ _ |- _ ] => destruct H as [H | H]
      | [ H : False |- _ ] => contradiction
      end; subst;
      simpl in Hx;
      (* Decompose the elements in the row *)
      repeat match goal with
      | [ H : _ \/ _ |- _ ] => destruct H as [H | H]
      | [ H : False |- _ ] => contradiction
      end; subst;
      (* Verify that x is either 0 or 1 *)
      lia.
    + (* Goal 3: Result calculation *)
      unfold sum_list, ceil_div.
      vm_compute.
      reflexivity.
Qed.