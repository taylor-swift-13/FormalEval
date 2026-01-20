Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.

Open Scope Z_scope.
Open Scope R_scope.
Open Scope string_scope.

Inductive value : Type :=
| VInt : Z -> value
| VFloat : R -> value
| VStr : string -> value.

Parameter replace_commas_with_dots : string -> string.
Parameter R_of_string : string -> R.

Definition num_of (v : value) : R :=
  match v with
  | VInt z => IZR z
  | VFloat r => r
  | VStr s => R_of_string (replace_commas_with_dots s)
  end.

Definition compare_one_spec (a : value) (b : value) (res : option value) : Prop :=
  let ra := num_of a in
  let rb := num_of b in
  (ra = rb /\ res = None) \/
  (Rlt rb ra /\ res = Some a) \/
  (Rlt ra rb /\ res = Some b).

(* Test case: input = [1%Z; 2%Z], output = 2%Z *)
Example test_compare_1_2 : compare_one_spec (VInt 1) (VInt 2) (Some (VInt 2)).
Proof.
  unfold compare_one_spec.
  unfold num_of.
  (* We need to prove the third disjunct: 1 < 2 and result is 2 *)
  right. right.
  split.
  - (* Prove IZR 1 < IZR 2 *)
    apply IZR_lt.
    (* Prove 1 < 2 in Z by computation *)
    compute. reflexivity.
  - (* Prove Some (VInt 2) = Some (VInt 2) *)
    reflexivity.
Qed.