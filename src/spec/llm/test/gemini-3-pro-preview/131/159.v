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

Example test_digits_spec_large : digits_spec 182937457814614279640075438629345987263878749129823578184719333882440 791461841690724789375.
Proof.
  exists [1; 8; 2; 9; 3; 7; 4; 5; 7; 8; 1; 4; 6; 1; 4; 2; 7; 9; 6; 4; 0; 0; 7; 5; 4; 3; 8; 6; 2; 9; 3; 4; 5; 9; 8; 7; 2; 6; 3; 8; 7; 8; 7; 4; 9; 1; 2; 9; 8; 2; 3; 5; 7; 8; 1; 8; 4; 7; 1; 9; 3; 3; 3; 8; 8; 2; 4; 4; 0].
  split.
  - repeat (constructor; try lia).
  - split.
    + vm_compute. reflexivity.
    + split.
      * intro. vm_compute. discriminate.
      * split.
        -- intro H. vm_compute in H. discriminate.
        -- intro. vm_compute. reflexivity.
Qed.