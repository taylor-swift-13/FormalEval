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

Example test_digits_5 : digits_spec 5 5.
Proof.
  unfold digits_spec.
  exists [5].
  split.
  - (* Forall (fun d => 0 <= d < 10) [5] *)
    constructor.
    + lia.
    + constructor.
  - split.
    + (* fold_left (fun acc d => 10 * acc + d) [5] 0 = 5 *)
      simpl. reflexivity.
    + split.
      * (* [5] <> [] -> hd 0 [5] <> 0 *)
        intros _. simpl. lia.
      * (* let odds := filter Z.odd [5] in ... *)
        simpl.
        split.
        -- (* [5] = [] -> 5 = 0 *)
           intros H. discriminate H.
        -- (* [5] <> [] -> 5 = fold_right Z.mul 1 [5] *)
           intros _. simpl. reflexivity.
Qed.