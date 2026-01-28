Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition digits_spec (n : Z) (res : Z) : Prop :=
  exists l : list Z,
    Forall (fun d => 0 <= d < 10) l /\
    fold_left (fun acc d => 10 * acc + d) l 0 = n /\
    (l <> [] -> hd 0 l <> 0) /\
    let odds := filter Z.odd l in
    (odds = [] -> res = 0) /\
    (odds <> [] -> res = fold_right Z.mul 1 odds).

Example test_digits_spec_large : digits_spec 124834738571930288374895092375830274843252127479238048384758941827309258429539458173975894729347582 47338934509524145086063972158203125.
Proof.
  exists [1; 2; 4; 8; 3; 4; 7; 3; 8; 5; 7; 1; 9; 3; 0; 2; 8; 8; 3; 7; 4; 8; 9; 5; 0; 9; 2; 3; 7; 5; 8; 3; 0; 2; 7; 4; 8; 4; 3; 2; 5; 2; 1; 2; 7; 4; 7; 9; 2; 3; 8; 0; 4; 8; 3; 8; 4; 7; 5; 8; 9; 4; 1; 8; 2; 7; 3; 0; 9; 2; 5; 8; 4; 2; 9; 5; 3; 9; 4; 5; 8; 1; 7; 3; 9; 7; 5; 8; 9; 4; 7; 2; 9; 3; 4; 7; 5; 8; 2].
  split.
  - repeat (constructor; try lia).
  - split.
    + vm_compute. reflexivity.
    + split.
      * intro. vm_compute. lia.
      * vm_compute. split.
        -- intro H. discriminate.
        -- intro H. reflexivity.
Qed.