Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Open Scope string_scope.
Open Scope Z_scope.

Fixpoint correct_bracketing_aux (s : string) (cnt : Z) : bool :=
  match s with
  | EmptyString => Z.eqb cnt 0
  | String c s' =>
      let cnt1 :=
        if Ascii.eqb c (Ascii.ascii_of_nat 40) then Z.succ cnt
        else if Ascii.eqb c (Ascii.ascii_of_nat 41) then Z.pred cnt
        else cnt in
      if Z.ltb cnt1 0 then false else correct_bracketing_aux s' cnt1
  end.

Definition correct_bracketing_fun (brackets : string) : bool :=
  correct_bracketing_aux brackets 0%Z.

Definition correct_bracketing_spec (brackets : string) (res : bool) : Prop :=
  res = correct_bracketing_fun brackets.

Example test_case: correct_bracketing_spec "()" true.
Proof.
  unfold correct_bracketing_spec.
  unfold correct_bracketing_fun.
  vm_compute.
  reflexivity.
Qed.