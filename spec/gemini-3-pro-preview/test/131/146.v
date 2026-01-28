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

Example test_digits_spec_large : digits_spec 3902482539585903843732859374089573948579380957409378540930757943758435987234095873947598341 49916370425944486485481990928031005859375.
Proof.
  exists [3; 9; 0; 2; 4; 8; 2; 5; 3; 9; 5; 8; 5; 9; 0; 3; 8; 4; 3; 7; 3; 2; 8; 5; 9; 3; 7; 4; 0; 8; 9; 5; 7; 3; 9; 4; 8; 5; 7; 9; 3; 8; 0; 9; 5; 7; 4; 0; 9; 3; 7; 8; 5; 4; 0; 9; 3; 0; 7; 5; 7; 9; 4; 3; 7; 5; 8; 4; 3; 5; 9; 8; 7; 2; 3; 4; 0; 9; 5; 8; 7; 3; 9; 4; 7; 5; 9; 8; 3; 4; 1].
  split.
  - repeat constructor; lia.
  - split.
    + vm_compute. reflexivity.
    + split.
      * intros H. vm_compute. lia.
      * vm_compute. split.
        -- intros H. discriminate H.
        -- intros H. reflexivity.
Qed.