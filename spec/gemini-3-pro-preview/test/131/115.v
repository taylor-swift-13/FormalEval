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

Example test_digits_spec_huge : digits_spec 1234567891011121314151617181920212223242526272829303132333435363738394041424344454647484950515253 83439724563916998046875.
Proof.
  exists [1; 2; 3; 4; 5; 6; 7; 8; 9; 1; 0; 1; 1; 1; 2; 1; 3; 1; 4; 1; 5; 1; 6; 1; 7; 1; 8; 1; 9; 2; 0; 2; 1; 2; 2; 2; 3; 2; 4; 2; 5; 2; 6; 2; 7; 2; 8; 2; 9; 3; 0; 3; 1; 3; 2; 3; 3; 3; 4; 3; 5; 3; 6; 3; 7; 3; 8; 3; 9; 4; 0; 4; 1; 4; 2; 4; 3; 4; 4; 4; 5; 4; 6; 4; 7; 4; 8; 4; 9; 5; 0; 5; 1; 5; 2; 5; 3].
  split.
  - repeat constructor. all: lia.
  - split.
    + vm_compute. reflexivity.
    + split.
      * intros _. vm_compute. discriminate.
      * vm_compute. split.
        -- intros H. discriminate.
        -- intros _. reflexivity.
Qed.