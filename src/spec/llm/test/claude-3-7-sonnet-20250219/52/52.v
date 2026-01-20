Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.

Definition below_threshold_spec_bool (l : list bool) (t : Z) (res : bool) : Prop :=
  res = forallb (fun x => match x with
                         | true => Z.ltb 0 t
                         | false => Z.ltb (-1) t
                         end) l.

Example test_below_threshold_bool :
  below_threshold_spec_bool [true; false; false] (-4) false.
Proof.
  unfold below_threshold_spec_bool.
  simpl.
  reflexivity.
Qed.