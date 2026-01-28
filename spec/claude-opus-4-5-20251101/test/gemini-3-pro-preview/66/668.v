Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition is_upper (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (Nat.leb 65 n) (Nat.leb n 90).

Definition ascii_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c).

Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c rest => c :: string_to_list rest
  end.

Definition sum_upper_ascii (chars : list ascii) : Z :=
  fold_right (fun c acc => if is_upper c then ascii_to_Z c + acc else acc) 0 chars.

Definition digitSum_spec (s : string) (result : Z) : Prop :=
  result = sum_upper_ascii (string_to_list s).

Example test_digitSum_long : digitSum_spec "Th!s!s$0nly4t3st!ng-f5mm5g55gn5t5Th5t5yn5thy5ht5t5S5t5b5t5m5t5nm5t4K5t5ms5t5m5t5nt5t5r5testt5s5t5n5n5M5t5s5t5m5t5sn5ST5TS5t5n5t5n5t5Ar5t5pn5t5shr5t5SS5t5v5t5sn5t5M5t1A$Bc&Def3@F5n" 1314%Z.
Proof.
  unfold digitSum_spec.
  vm_compute.
  reflexivity.
Qed.