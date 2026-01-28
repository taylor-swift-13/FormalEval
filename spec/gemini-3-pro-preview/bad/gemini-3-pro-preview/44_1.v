Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition char_to_digit (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c) - Z.of_nat (nat_of_ascii "0"%char).

Fixpoint string_to_val (s : string) (base : Z) : Z :=
  match s with
  | EmptyString => 0
  | String c s' => 
      char_to_digit c * (Z.pow base (Z.of_nat (length s'))) + string_to_val s' base
  end.

Fixpoint valid_digits (s : string) (base : Z) : Prop :=
  match s with
  | EmptyString => True
  | String c s' => 
      0 <= char_to_digit c < base /\ valid_digits s' base
  end.

Definition is_canonical (s : string) : Prop :=
  match s with
  | String "0"%char _ => False 
  | _ => True
  end.

Definition change_base_spec (x : Z) (base : Z) (ret : string) : Prop :=
  2 <= base < 10 ->
  x >= 0 ->
  (x = 0 -> ret = "0") /\
  (x > 0 -> 
    valid_digits ret base /\
    string_to_val ret base = x /\
    is_canonical ret).

Example test_change_base_8_3 : change_base_spec 8 3 "22".
Proof.
  unfold change_base_spec.
  intros Hbase Hx.
  split.
  - (* Case x = 0 *)
    intro H_eq.
    discriminate H_eq.
  - (* Case x > 0 *)
    intro H_gt.
    repeat split.
    + (* valid_digits *)
      unfold valid_digits.
      vm_compute. (* Computes char_to_digit values and reduces structure *)
      repeat split; lia.
    + (* string_to_val *)
      unfold string_to_val.
      vm_compute. (* Computes the value: 2*3^1 + 2*3^0 = 8 *)
      reflexivity.
    + (* is_canonical *)
      unfold is_canonical.
      vm_compute. (* Checks "22" does not start with "0" *)
      trivial.
Qed.