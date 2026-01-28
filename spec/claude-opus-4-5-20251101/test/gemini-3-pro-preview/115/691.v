Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Lia.

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

Example test_max_fill : max_fill_spec [[0; 0; 0; 1]; [0; 1; 1; 1]; [0; 0; 0; 1]; [0; 0; 0; 1]; [0; 1; 1; 1]; [0; 1; 1; 1]; [0; 0; 0; 1]] 6 7.
Proof.
  unfold max_fill_spec.
  split.
  - (* Prove capacity > 0 *)
    lia.
  - split.
    + (* Prove all elements in the grid are 0 or 1 *)
      intros row Hrow x Hx.
      simpl in Hrow.
      (* Decompose the rows *)
      repeat (destruct Hrow as [Hrow | Hrow]; [subst; simpl in Hx; intuition; try lia | ]).
      contradiction.
    + (* Prove the result calculation *)
      unfold sum_list, ceil_div.
      simpl.
      reflexivity.
Qed.