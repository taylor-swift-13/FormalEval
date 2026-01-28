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

Example test_digits_spec_15 : digits_spec 15 5.
Proof.
  exists [1; 5].
  split.
  - (* Prove: Forall (fun d => 0 <= d < 10) [1; 5] *)
    constructor.
    + lia.
    + constructor.
      * lia.
      * constructor.
  - split.
    + (* Prove: fold_left ... = 15 *)
      simpl. reflexivity.
    + split.
      * (* Prove: [1; 5] <> [] -> hd 0 [1; 5] <> 0 *)
        intros H. simpl. lia.
      * (* Prove parts related to 'odds' *)
        simpl. (* Reduces filter Z.odd [1; 5] to [1; 5] *)
        split.
        -- (* Prove: [1; 5] = [] -> 5 = 0 *)
           intros H. discriminate H.
        -- (* Prove: [1; 5] <> [] -> 5 = fold_right Z.mul 1 [1; 5] *)
           intros H. simpl. reflexivity.
Qed.