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

Example test_digits_spec_huge : digits_spec 323456789101112131415161718192021222324252627282930313233343532 83053267329375.
Proof.
  exists [3; 2; 3; 4; 5; 6; 7; 8; 9; 1; 0; 1; 1; 1; 2; 1; 3; 1; 4; 1; 5; 1; 6; 1; 7; 1; 8; 1; 9; 2; 0; 2; 1; 2; 2; 2; 3; 2; 4; 2; 5; 2; 6; 2; 7; 2; 8; 2; 9; 3; 0; 3; 1; 3; 2; 3; 3; 3; 4; 3; 5; 3; 2].
  split.
  - repeat (constructor; [lia | ]). constructor.
  - split.
    + vm_compute. reflexivity.
    + split.
      * intro H. vm_compute. discriminate.
      * vm_compute. split.
        -- intro H. discriminate.
        -- intro H. reflexivity.
Qed.