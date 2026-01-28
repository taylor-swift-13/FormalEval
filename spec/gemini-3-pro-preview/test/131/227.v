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

Example test_digits_spec_large : digits_spec 8843924584737538929273870549395092387583092748327447402387489518947358439582352938 27602877265028656026859458984375.
Proof.
  exists [8; 8; 4; 3; 9; 2; 4; 5; 8; 4; 7; 3; 7; 5; 3; 8; 9; 2; 9; 2; 7; 3; 8; 7; 0; 5; 4; 9; 3; 9; 5; 0; 9; 2; 3; 8; 7; 5; 8; 3; 0; 9; 2; 7; 4; 8; 3; 2; 7; 4; 4; 7; 4; 0; 2; 3; 8; 7; 4; 8; 9; 5; 1; 8; 9; 4; 7; 3; 5; 8; 4; 3; 9; 5; 8; 2; 3; 5; 2; 9; 3; 8].
  split.
  - repeat (constructor; try lia).
  - split.
    + vm_compute. reflexivity.
    + split.
      * intros H. vm_compute. discriminate.
      * vm_compute. split.
        -- intros H. discriminate H.
        -- intros H. reflexivity.
Qed.