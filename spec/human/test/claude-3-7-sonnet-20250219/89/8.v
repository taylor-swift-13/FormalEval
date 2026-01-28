Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope char_scope.
Open Scope string_scope.
Open Scope nat_scope.

Definition char_relation (c_in c_out : ascii) : Prop :=
  match c_in with
  | "a"%char => c_out = "e"%char | "b"%char => c_out = "f"%char | "c"%char => c_out = "g"%char | "d"%char => c_out = "h"%char
  | "e"%char => c_out = "i"%char | "f"%char => c_out = "j"%char | "g"%char => c_out = "k"%char | "h"%char => c_out = "l"%char
  | "i"%char => c_out = "m"%char | "j"%char => c_out = "n"%char | "k"%char => c_out = "o"%char | "l"%char => c_out = "p"%char
  | "m"%char => c_out = "q"%char | "n"%char => c_out = "r"%char | "o"%char => c_out = "s"%char | "p"%char => c_out = "t"%char
  | "q"%char => c_out = "u"%char | "r"%char => c_out = "v"%char | "s"%char => c_out = "w"%char | "t"%char => c_out = "x"%char
  | "u"%char => c_out = "y"%char | "v"%char => c_out = "z"%char | "w"%char => c_out = "a"%char | "x"%char => c_out = "b"%char
  | "y"%char => c_out = "c"%char | "z"%char => c_out = "d"%char
  | _ => c_out = c_in
  end.

Definition problem_89_spec (s : string) (output : string) : Prop :=
  String.length s = String.length output /\
  forall i, i < String.length s ->
    match String.get i s, String.get i output with
    | Some c_in, Some c_out => char_relation c_in c_out
    | _, _ => False
    end.

Example encrypt_a :
  problem_89_spec "a" "e".
Proof.
  unfold problem_89_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    destruct i as [| i'].
    + simpl. reflexivity.
    + simpl in Hi. lia.
Qed.